#!/usr/bin/env python3
import json
import math
import os
import random
import re
import shutil
import sqlite3
import subprocess
import threading
from ctypes import byref, c_int, c_uint, c_ulong, c_void_p, cdll
import tkinter as tk
from dataclasses import asdict, dataclass
from datetime import date, datetime, timedelta
from pathlib import Path
from tkinter import font

import gi

gi.require_version("Gtk", "3.0")
from gi.repository import Gtk


APP_DIR = Path(__file__).resolve().parent
DATA_FILE = APP_DIR / "tasks.json"
SETTINGS_FILE = APP_DIR / "settings.json"
DAILY_STATUS_FILE = APP_DIR / "daily_status.json"
TRAY_ICON_FILE = APP_DIR / "assets" / "tray_icon.png"
HISTORY_ROOT = APP_DIR / "history"
LEGACY_HISTORY_DB_FILE = APP_DIR / "daily_history.sqlite3"
MONTH_HISTORY_DB_NAME = "daily_records.sqlite3"
MONTH_HISTORY_JSONL_NAME = "daily_records.jsonl"
MONTH_HISTORY_README_NAME = "README.txt"
WINDOW_WIDTH = 720
WINDOW_HEIGHT = 740
MIN_WINDOW_WIDTH = 560
MIN_WINDOW_HEIGHT = 560
BUTTON_MASKS = 0x100 | 0x200 | 0x400 | 0x800 | 0x1000
REVERT_TO_PARENT = 2
CURRENT_TIME = 0

DEFAULT_SETTINGS = {
    "accent": "#ff6fa8",
    "background": "#050507",
    "text": "#ffd6e6",
    "done": "#76a7ff",
    "geometry": "",
    "active_date": "",
    "title_font_size": 20,
    "body_font_size": 16,
    "small_font_size": 12,
    "icon_font_size": 20,
}

REPEAT_OPTIONS = ("单次", "每天", "工作日", "自定义")
WEEKDAY_LABELS = ("周一", "周二", "周三", "周四", "周五", "周六", "周日")

ACCENT_COLORS = [
    "#ff6fa8",
    "#ff4f92",
    "#ff2f6d",
    "#ff8a5c",
    "#ff5f45",
    "#ffd166",
    "#f8c537",
    "#e7f05b",
    "#62d196",
    "#2fd37f",
    "#15c6a8",
    "#55c7ff",
    "#3498ff",
    "#4f7cff",
    "#8a7cff",
    "#6d5dfc",
    "#c77dff",
    "#a855f7",
    "#f472b6",
    "#fb7185",
    "#f97316",
    "#22c55e",
    "#06b6d4",
    "#e879f9",
    "#ffffff",
]

BACKGROUND_COLORS = [
    "#050507",
    "#000000",
    "#151515",
    "#202124",
    "#1a1020",
    "#241126",
    "#33152d",
    "#0f172a",
    "#111827",
    "#172554",
    "#10231d",
    "#0f2f24",
    "#123026",
    "#2a1616",
    "#3a1717",
    "#3b2416",
    "#2c230b",
    "#1f2937",
    "#334155",
    "#4a044e",
    "#581c87",
    "#7f1d1d",
    "#7c2d12",
    "#064e3b",
    "#0e7490",
    "#f8e8ef",
    "#fce7f3",
    "#e0f2fe",
    "#dcfce7",
    "#fef3c7",
    "#fff7cf",
]


@dataclass
class Task:
    text: str
    done: bool = False
    repeat: str = "单次"
    starred: bool = False
    custom: dict | None = None
    created_on: str = ""


class DesktopTodo:
    def __init__(self) -> None:
        self.settings = self.load_settings()
        self.daily_status = self.load_daily_status()
        self.root = tk.Tk()
        self.root.title("今日待办")
        self.root.configure(bg=self.settings["background"])
        self.root.overrideredirect(True)
        self.root.resizable(True, True)
        self.root.minsize(MIN_WINDOW_WIDTH, MIN_WINDOW_HEIGHT)
        self.root.attributes("-topmost", True)
        self.root.bind("<Map>", self.restore_borderless)
        self.root.bind("<Escape>", lambda _event: self.minimize_window())
        self.root.bind("<Control-q>", lambda _event: self.minimize_window())

        self.tasks = self.load_tasks()
        self.init_history_storage()
        self.archive_due_days()
        self.drag_start_x = 0
        self.drag_start_y = 0
        self.resize_start_x = 0
        self.resize_start_y = 0
        self.resize_start_width = WINDOW_WIDTH
        self.resize_start_height = WINDOW_HEIGHT
        self.resize_start_root_x = 0
        self.resize_start_root_y = 0
        self.resize_mode = "corner"
        self.color_popup = None
        self.font_popup = None
        self.repeat_popup = None
        self.commute_popup = None
        self.custom_popup = None
        self.task_list_popup = None
        self.context_popup = None
        self.rename_popup = None
        self.rename_save_callback = None
        self.history_popup = None
        self.history_body = None
        self.history_selected_day = None
        self.history_completed = []
        self.history_incomplete = []
        self.status_icon = None
        self.status_menu = None
        self.gtk_thread = None
        self.hide_after_id = None
        self.outside_watch_id = None
        self.work_timer_after_id = None
        self.x11 = self.init_x11()
        self.last_pointer_buttons = 0
        self.window_locked = False
        self.always_on_top = tk.BooleanVar(value=True)
        self.new_task = tk.StringVar()
        self.new_repeat = tk.StringVar(value="单次")
        self.new_custom = None
        self.current_day_key = date.today().isoformat()
        self.today_all_done = False
        self.celebration_enabled = False
        self.firework_canvas = None
        self.firework_overlay = None
        self.firework_after_ids = []
        self.expanded_interval_labels = set()

        self.title_font = self.make_font("title_font_size")
        self.body_font = self.make_font("body_font_size")
        self.small_font = self.make_font("small_font_size")
        self.icon_font = self.make_font("icon_font_size")

        self.place_top_right()
        self.build_ui()
        self.apply_theme()
        self.render_tasks()
        self.setup_status_icon()
        self.schedule_midnight_rollover()
        self.root.withdraw()
        self.celebration_enabled = True

    def place_top_right(self) -> None:
        self.root.update_idletasks()
        x, y, width, _height = self.primary_monitor_geometry()
        window_width = WINDOW_WIDTH
        window_height = WINDOW_HEIGHT
        window_x = x + width - window_width - 24
        window_y = y + 58
        self.root.geometry(f"{window_width}x{window_height}+{window_x}+{window_y}")

    def primary_monitor_geometry(self) -> tuple[int, int, int, int]:
        try:
            output = subprocess.check_output(["xrandr", "--query"], text=True, stderr=subprocess.DEVNULL)
        except Exception:
            return 0, 0, self.root.winfo_screenwidth(), self.root.winfo_screenheight()

        pattern = re.compile(r"\bprimary\s+(\d+)x(\d+)\+(-?\d+)\+(-?\d+)")
        for line in output.splitlines():
            match = pattern.search(line)
            if match:
                width, height, x, y = map(int, match.groups())
                return x, y, width, height

        pattern = re.compile(r"\bconnected\s+(\d+)x(\d+)\+(-?\d+)\+(-?\d+)")
        for line in output.splitlines():
            match = pattern.search(line)
            if match:
                width, height, x, y = map(int, match.groups())
                return x, y, width, height

        return 0, 0, self.root.winfo_screenwidth(), self.root.winfo_screenheight()

    def build_ui(self) -> None:
        self.panel = tk.Frame(
            self.root,
            bg=self.settings["background"],
            highlightthickness=2,
            bd=0,
        )
        self.panel.pack(fill="both", expand=True, padx=12, pady=12)
        self.root.bind("<FocusOut>", self.hide_after_external_click)
        self.root.bind("<ButtonPress-1>", self.focus_clicked_widget, add="+")
        self.root.bind_all("<ButtonPress-1>", self.lock_window_for_editing, add="+")

        self.header = tk.Frame(self.panel, cursor="fleur", bd=0)
        self.header.pack(fill="x", padx=18, pady=(16, 8))
        self.header.bind("<ButtonPress-1>", self.start_drag)
        self.header.bind("<B1-Motion>", self.drag_window)

        self.title_label = tk.Label(
            self.header,
            text="今日待办",
            font=self.title_font,
            anchor="w",
        )
        self.title_label.pack(side="left", fill="x", expand=True)
        self.title_label.bind("<ButtonPress-1>", self.start_drag)
        self.title_label.bind("<B1-Motion>", self.drag_window)

        self.header_actions = tk.Frame(self.header, bg=self.settings["background"])
        self.header_actions.pack(side="right")

        self.checkin_btn = tk.Button(
            self.header_actions,
            text="到岗",
            command=self.toggle_checkin,
            bd=0,
            font=self.small_font,
            highlightthickness=1,
        )
        self.checkin_btn.pack(side="left", padx=(0, 8), ipadx=8, ipady=2)

        self.commute_btn = tk.Button(
            self.header_actions,
            text="通勤:",
            command=self.show_commute_popup,
            bd=0,
            font=self.small_font,
            highlightthickness=1,
        )
        self.commute_btn.pack(side="left", ipadx=8, ipady=2)

        self.update_daily_status_buttons()
        self.schedule_work_timer_tick()

        self.date_label = tk.Label(
            self.header,
            text="",
            font=self.small_font,
            anchor="e",
        )
        self.date_label.bind("<ButtonPress-1>", self.start_drag)
        self.date_label.bind("<B1-Motion>", self.drag_window)

        self.progress_canvas = tk.Canvas(self.panel, height=8, bd=0, highlightthickness=0)
        self.progress_canvas.pack(fill="x", padx=20, pady=(2, 10))
        self.progress_canvas.bind("<Configure>", lambda _event: self.draw_progress())

        self.status_label = tk.Label(self.panel, text="", anchor="w", font=self.body_font)
        self.status_label.pack(fill="x", padx=20, pady=(0, 12))

        input_outer = tk.Frame(self.panel, highlightthickness=1, bd=0)
        input_outer.pack(fill="x", padx=18, pady=(0, 14))

        self.entry = tk.Entry(
            input_outer,
            textvariable=self.new_task,
            bd=0,
            font=self.body_font,
            insertwidth=2,
            takefocus=1,
        )
        self.entry.pack(side="left", fill="x", expand=True, padx=(8, 8), ipady=7)
        self.entry.insert(0, "")
        self.entry.bind("<Return>", lambda _event: self.add_task())
        self.entry.bind("<ButtonPress-1>", self.focus_entry, add="+")
        self.entry.bind("<ButtonRelease-1>", self.focus_entry, add="+")

        self.repeat_button = tk.Button(
            input_outer,
            text="频率",
            command=lambda: self.show_repeat_popup(self.repeat_button, self.create_task_with_repeat),
            bd=0,
            width=5,
            font=self.body_font,
        )
        self.repeat_button.pack(side="right", padx=(0, 8), pady=6, ipady=7)

        self.task_area = tk.Frame(self.panel, bd=0)
        self.task_area.pack(fill="both", expand=True, padx=14, pady=(0, 8))

        self.task_scrollbar = tk.Scrollbar(
            self.task_area,
            orient="vertical",
            command=self.task_canvas_scroll,
            bd=0,
            width=14,
            elementborderwidth=0,
            relief="flat",
            highlightthickness=0,
        )
        self.task_scrollbar.pack(side="right", fill="y")

        self.task_canvas = tk.Canvas(
            self.task_area,
            bd=0,
            highlightthickness=0,
            yscrollincrement=28,
            yscrollcommand=self.task_scrollbar.set,
        )
        self.task_canvas.pack(side="left", fill="both", expand=True)

        self.task_frame = tk.Frame(self.task_canvas)
        self.task_window = self.task_canvas.create_window((0, 0), window=self.task_frame, anchor="nw")
        self.task_canvas.bind("<Configure>", self.resize_task_window)
        self.task_frame.bind(
            "<Configure>",
            self.update_task_scroll_region,
        )
        for widget in (self.task_area, self.task_canvas, self.task_frame):
            self.bind_task_scroll_widget(widget)

        footer = tk.Frame(self.panel)
        footer.pack(fill="x", padx=18, pady=(0, 14))
        for column in range(5):
            footer.grid_columnconfigure(column, weight=1, uniform="footer")

        self.task_list_wrapper = tk.Frame(footer, bg=self.settings["background"])
        self.task_list_wrapper.grid(row=0, column=0, sticky="ew", padx=(0, 4), pady=(8, 0))

        self.task_list_btn = tk.Button(
            self.task_list_wrapper,
            text="任务列表",
            command=self.show_task_list_popup,
            bd=0,
            font=self.small_font,
            anchor="center",
        )
        self.task_list_btn.pack(fill="x", padx=(0, 10), ipady=4)

        self.task_count_badge = tk.Canvas(
            self.task_list_wrapper,
            bg="#e53935",
            width=30,
            height=30,
            bd=0,
            highlightthickness=0,
        )
        self.task_count_badge.place(relx=1, rely=0, x=0, y=0, anchor="ne")

        self.history_btn = tk.Button(
            footer,
            text="历史存档",
            command=self.show_history_popup,
            bd=0,
            font=self.small_font,
        )
        self.history_btn.grid(row=0, column=4, sticky="ew", padx=(4, 0), pady=(8, 0), ipady=4)

        self.color_btn = tk.Button(
            footer,
            text="字体颜色",
            command=self.choose_accent_color,
            bd=0,
            font=self.small_font,
        )
        self.color_btn.grid(row=0, column=3, sticky="ew", padx=4, pady=(8, 0), ipady=4)

        self.font_size_btn = tk.Button(
            footer,
            text="字体大小",
            command=self.show_font_size_popup,
            bd=0,
            font=self.small_font,
        )
        self.font_size_btn.grid(row=0, column=2, sticky="ew", padx=4, pady=(8, 0), ipady=4)

        self.bg_btn = tk.Button(
            footer,
            text="背景颜色",
            command=self.choose_background_color,
            bd=0,
            font=self.small_font,
        )
        self.bg_btn.grid(row=0, column=1, sticky="ew", padx=4, pady=(8, 0), ipady=4)

        self.right_resize_zone = tk.Frame(self.root, cursor="sb_h_double_arrow", width=4)
        self.right_resize_zone.place(relx=1, rely=0, relheight=1, anchor="ne")
        self.right_resize_zone.bind("<ButtonPress-1>", lambda event: self.start_resize(event, "right"))
        self.right_resize_zone.bind("<B1-Motion>", self.resize_window)

        self.bottom_resize_zone = tk.Frame(self.root, cursor="sb_v_double_arrow", height=4)
        self.bottom_resize_zone.place(relx=0, rely=1, relwidth=1, anchor="sw")
        self.bottom_resize_zone.bind("<ButtonPress-1>", lambda event: self.start_resize(event, "bottom"))
        self.bottom_resize_zone.bind("<B1-Motion>", self.resize_window)

        self.resize_handle = tk.Label(
            self.root,
            text="◢",
            cursor="bottom_right_corner",
            font=self.small_font,
            padx=6,
            pady=3,
        )
        self.resize_handle.place(relx=1, rely=1, anchor="se")
        self.resize_handle.bind("<ButtonPress-1>", lambda event: self.start_resize(event, "corner"))
        self.resize_handle.bind("<B1-Motion>", self.resize_window)

    def apply_theme(self) -> None:
        accent = self.settings["accent"]
        bg = self.settings["background"]
        text = self.settings["text"]
        done = self.settings["done"]
        entry_bg = self.mix(bg, "#ffffff", 0.08)
        row_bg = self.mix(bg, "#ffffff", 0.04)
        hover = self.mix(bg, "#ffffff", 0.12)

        self.root.configure(bg=bg)
        self.panel.configure(bg=bg, highlightbackground=accent, highlightcolor=accent)
        self.header.configure(bg=bg)
        self.header_actions.configure(bg=bg)
        self.title_label.configure(bg=bg, fg=text)
        self.date_label.configure(bg=bg, fg=text)
        for button in (self.checkin_btn, self.commute_btn):
            button.configure(
                bg=bg,
                fg=text,
                activebackground=hover,
                activeforeground=text,
                highlightbackground=text,
            )
        self.progress_canvas.configure(bg=bg)
        self.status_label.configure(bg=bg, fg=text)
        self.task_area.configure(bg=bg)
        self.task_canvas.configure(bg=bg)
        self.task_frame.configure(bg=bg)
        self.task_scrollbar.configure(
            bg=text,
            activebackground=text,
            troughcolor=self.mix(bg, "#ffffff", 0.18),
        )
        self.task_list_wrapper.configure(bg=bg)
        self.task_count_badge.configure(bg=bg)
        self.update_task_count_badge()

        for button in [
            self.task_list_btn,
            self.color_btn,
            self.font_size_btn,
            self.bg_btn,
            self.history_btn,
        ]:
            button.configure(
                bg=bg,
                fg=text,
                activebackground=hover,
                activeforeground=text,
            )

        self.resize_handle.configure(bg=bg, fg=accent)
        self.right_resize_zone.configure(bg=bg)
        self.bottom_resize_zone.configure(bg=bg)
        for child in self.panel.winfo_children():
            if isinstance(child, tk.Frame):
                child.configure(bg=bg)

        for child in self.panel.winfo_children():
            if isinstance(child, tk.Frame) and child.winfo_children():
                for grandchild in child.winfo_children():
                    if isinstance(grandchild, tk.Entry):
                        grandchild.configure(
                            bg=entry_bg,
                            fg=text,
                            insertbackground=accent,
                        )
                    elif isinstance(grandchild, tk.Button):
                        grandchild.configure(
                            bg=bg,
                            fg=accent,
                            activebackground=hover,
                            activeforeground=text,
                        )
                    elif isinstance(grandchild, tk.Menubutton):
                        grandchild.configure(
                            bg=bg,
                            fg=text,
                            activebackground=hover,
                            activeforeground=text,
                            highlightthickness=1,
                            highlightbackground=text,
                        )
                        grandchild["menu"].configure(
                            bg=bg,
                            fg=text,
                            activebackground=hover,
                            activeforeground=text,
                        )

        self.repeat_button.configure(
            bg=bg,
            fg=text,
            activebackground=hover,
            activeforeground=text,
            highlightthickness=1,
            highlightbackground=text,
        )
        self.done_color = done
        self.row_bg = row_bg
        self.entry_bg = entry_bg
        self.draw_progress()

    def render_tasks(self) -> None:
        for child in self.task_frame.winfo_children():
            child.destroy()

        visible_tasks = self.visible_tasks()
        if not visible_tasks:
            tk.Label(
                self.task_frame,
                text="还没有安排，先添加一件事。",
                bg=self.settings["background"],
                fg=self.settings["text"],
                font=self.body_font,
            ).pack(anchor="center", pady=42)
        else:
            for task in visible_tasks:
                self.render_task(task)

        done_count = sum(1 for task in visible_tasks if task.done)
        self.status_label.configure(text=f"{done_count} / {len(visible_tasks)} 已完成")
        self.update_task_count_badge()
        self.draw_progress()
        self.maybe_celebrate_completion(visible_tasks, done_count)

    def maybe_celebrate_completion(self, visible_tasks: list[Task], done_count: int) -> None:
        all_done = bool(visible_tasks) and done_count == len(visible_tasks)
        should_celebrate = (
            self.celebration_enabled
            and all_done
            and not self.today_all_done
            and self.root.state() != "withdrawn"
        )
        self.today_all_done = all_done
        if should_celebrate:
            self.start_fireworks()

    def start_fireworks(self) -> None:
        self.stop_fireworks()
        self.root.update_idletasks()
        width = max(220, self.task_area.winfo_width())
        height = max(220, self.task_area.winfo_height())
        x = self.task_area.winfo_rootx()
        y = self.task_area.winfo_rooty()
        transparent = "#010203"

        overlay = tk.Toplevel(self.root)
        overlay.overrideredirect(True)
        overlay.attributes("-topmost", True)
        overlay.geometry(f"{width}x{height}+{x}+{y}")
        overlay.configure(bg=transparent)
        try:
            overlay.wm_attributes("-transparentcolor", transparent)
        except tk.TclError:
            overlay.attributes("-alpha", 0.9)
            transparent = self.settings["background"]
            overlay.configure(bg=transparent)

        canvas = tk.Canvas(
            overlay,
            bg=transparent,
            bd=0,
            highlightthickness=0,
        )
        canvas.pack(fill="both", expand=True)
        self.firework_overlay = overlay
        self.firework_canvas = canvas

        palette = [
            self.settings["accent"],
            self.settings["done"],
            "#ffffff",
            "#ffd166",
            "#62d196",
            "#55c7ff",
            "#f472b6",
        ]
        bursts = [
            (width * 0.26, height * 0.24),
            (width * 0.68, height * 0.28),
            (width * 0.48, height * 0.44),
        ]
        particles = []
        for center_x, center_y in bursts:
            for index in range(28):
                angle = (math.tau / 28) * index + random.uniform(-0.08, 0.08)
                speed = random.uniform(4.0, 8.5)
                particles.append(
                    {
                        "x": center_x,
                        "y": center_y,
                        "vx": math.cos(angle) * speed,
                        "vy": math.sin(angle) * speed,
                        "color": random.choice(palette),
                        "size": random.uniform(2.5, 5.5),
                    }
                )
        canvas.create_text(
            width / 2,
            height * 0.38,
            text="今日任务完成",
            fill=self.settings["text"],
            font=self.title_font,
            tags=("firework", "firework_message"),
        )
        canvas.create_text(
            width / 2,
            height * 0.46,
            text="休息一下也很好",
            fill=self.mix(self.settings["text"], self.settings["background"], 0.22),
            font=self.small_font,
            tags=("firework", "firework_message"),
        )
        canvas.tag_raise("firework")
        self.animate_fireworks(canvas, particles, 0)

    def animate_fireworks(self, canvas: tk.Canvas, particles: list[dict], frame: int) -> None:
        if self.firework_canvas is not canvas or not canvas.winfo_exists():
            return
        canvas.delete("firework_spark")
        fade = max(0.0, 1.0 - frame / 42)
        for particle in particles:
            particle["x"] += particle["vx"]
            particle["y"] += particle["vy"]
            particle["vy"] += 0.16
            particle["vx"] *= 0.985
            particle["vy"] *= 0.985
            radius = max(1.0, particle["size"] * fade)
            canvas.create_oval(
                particle["x"] - radius,
                particle["y"] - radius,
                particle["x"] + radius,
                particle["y"] + radius,
                fill=particle["color"],
                outline="",
                tags=("firework", "firework_spark"),
            )
        canvas.tag_raise("firework")

        if frame >= 42:
            self.stop_fireworks()
            return
        after_id = self.root.after(38, lambda: self.animate_fireworks(canvas, particles, frame + 1))
        self.firework_after_ids.append(after_id)

    def stop_fireworks(self) -> None:
        for after_id in self.firework_after_ids:
            try:
                self.root.after_cancel(after_id)
            except Exception:
                pass
        self.firework_after_ids = []
        if self.firework_canvas is not None and self.firework_canvas.winfo_exists():
            self.firework_canvas.delete("firework")
        self.firework_canvas = None
        if self.firework_overlay is not None and self.firework_overlay.winfo_exists():
            self.firework_overlay.destroy()
        self.firework_overlay = None

    def update_task_count_badge(self) -> None:
        count = str(len(self.tasks))
        self.task_count_badge.delete("all")
        self.task_count_badge.create_oval(3, 3, 29, 29, fill="#e53935", outline="#e53935")
        self.task_count_badge.create_text(16, 16, text=count, fill="#ffffff", font=self.small_font)

    def visible_tasks(self) -> list[Task]:
        return self.sorted_tasks_for_display(self.tasks_for_date(self.tasks, date.today()))

    def sorted_tasks_for_display(self, tasks: list[Task]) -> list[Task]:
        indexed_tasks = list(enumerate(tasks))
        indexed_tasks.sort(key=lambda item: (1 if item[1].done else 0, 0 if item[1].starred else 1, item[0]))
        return [task for _index, task in indexed_tasks]

    def tasks_for_date(self, tasks: list[Task], day: date) -> list[Task]:
        visible = []
        for task in tasks:
            if task.repeat == "工作日" and day.weekday() >= 5:
                continue
            if task.repeat == "自定义" and not self.is_custom_due(task, day):
                continue
            visible.append(task)
        return visible

    def render_task(self, task: Task) -> None:
        task_bg = self.pinned_task_bg(task)
        row = tk.Frame(self.task_frame, bg=task_bg)
        row.pack(fill="x", pady=0)

        line = tk.Frame(row, bg=self.settings["accent"], height=1)
        line.pack(side="bottom", fill="x", padx=4)

        content = tk.Frame(row, bg=task_bg)
        content.pack(fill="x", padx=0, pady=8)

        check = tk.Button(
            content,
            text="✓" if task.done else "○",
            command=lambda selected=task: self.toggle_task(selected),
            bd=0,
            width=2,
            font=self.icon_font,
            bg=task_bg,
            fg=self.done_color if task.done else self.settings["accent"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
        )
        check.pack(side="left", padx=(2, 8))

        text = tk.Label(
            content,
            text=task.text,
            anchor="w",
            bg=task_bg,
            fg=self.settings["text"] if not task.done else self.mix(self.settings["text"], self.settings["background"], 0.42),
            font=self.body_font,
            justify="left",
            wraplength=210,
        )
        text.pack(side="left", fill="x", expand=True)
        if task.done:
            text.configure(
                font=font.Font(
                    family="Noto Sans CJK SC",
                    size=-self.font_setting("body_font_size"),
                    weight="bold",
                    overstrike=True,
                )
            )

        repeat_button = tk.Button(
            content,
            text=self.repeat_label(task),
            bd=0,
            width=8,
            font=self.small_font,
            bg=task_bg,
            fg=self.settings["text"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )
        repeat_button.configure(
            command=lambda selected=task, anchor=repeat_button: self.show_repeat_popup(
                anchor,
                lambda value, custom=None, selected=selected: self.update_repeat(selected, value, custom),
            )
        )
        repeat_button.pack(side="left", padx=(8, 8))

        delete_button = tk.Button(
            content,
            text="×",
            command=lambda selected=task: self.delete_task(selected),
            bd=0,
            width=2,
            font=self.icon_font,
            bg=task_bg,
            fg=self.settings["accent"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
        )
        delete_button.pack(side="right")

        row.bind("<Configure>", lambda event, label=text: label.configure(wraplength=max(90, event.width - 220)))
        for widget in (row, line, content, check, text, repeat_button, delete_button):
            self.bind_task_scroll_widget(widget)
            widget.bind("<Button-3>", lambda event, selected=task: self.show_task_context_menu(event, selected))

    def pinned_task_bg(self, task: Task) -> str:
        if task.starred and not task.done:
            return self.mix(self.settings["background"], self.settings["accent"], 0.1)
        return self.settings["background"]

    def show_task_list_popup(self) -> None:
        self.stop_fireworks()
        self.close_task_list_popup()
        self.close_history_popup()
        self.close_commute_popup()
        self.close_color_popup()
        self.close_font_popup()
        self.close_repeat_popup()
        self.close_custom_popup()

        popup = tk.Toplevel(self.root)
        self.task_list_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=2,
            highlightbackground=self.settings["text"],
        )

        popup_width = 560
        popup_height = 560
        x = self.root.winfo_rootx() + max(24, self.root.winfo_width() - popup_width - 24)
        y = self.root.winfo_rooty() + 84
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")

        top = tk.Frame(popup, bg=self.settings["background"])
        top.pack(fill="x", padx=14, pady=(12, 8))
        tk.Label(
            top,
            text=f"任务列表 · 共 {len(self.tasks)} 项",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.body_font,
        ).pack(side="left")
        tk.Button(
            top,
            text="×",
            command=self.close_task_list_popup,
            bd=0,
            width=2,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.body_font,
        ).pack(side="right")

        area = tk.Frame(popup, bg=self.settings["background"])
        area.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        scrollbar = tk.Scrollbar(area, orient="vertical", bd=0, width=12, highlightthickness=0)
        scrollbar.pack(side="right", fill="y")
        canvas = tk.Canvas(
            area,
            bd=0,
            highlightthickness=0,
            bg=self.settings["background"],
            yscrollincrement=28,
            yscrollcommand=scrollbar.set,
        )
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.configure(
            command=canvas.yview,
            bg=self.settings["text"],
            activebackground=self.settings["text"],
            troughcolor=self.mix(self.settings["background"], "#ffffff", 0.18),
        )

        frame = tk.Frame(canvas, bg=self.settings["background"])
        window = canvas.create_window((0, 0), window=frame, anchor="nw")

        def update_region(_event: tk.Event | None = None) -> None:
            canvas.configure(scrollregion=canvas.bbox("all"))

        def resize_body(event: tk.Event) -> None:
            canvas.itemconfigure(window, width=event.width)
            update_region()

        def scroll_popup(event: tk.Event) -> str:
            if getattr(event, "num", None) == 4:
                canvas.yview_scroll(-3, "units")
            elif getattr(event, "num", None) == 5:
                canvas.yview_scroll(3, "units")
            else:
                direction = -1 if event.delta > 0 else 1
                canvas.yview_scroll(direction * 3, "units")
            return "break"

        canvas.bind("<Configure>", resize_body)
        frame.bind("<Configure>", update_region)

        if not self.tasks:
            tk.Label(
                frame,
                text="还没有创建任务。",
                bg=self.settings["background"],
                fg=self.settings["text"],
                font=self.body_font,
            ).pack(anchor="center", pady=42)
        else:
            for task in self.sorted_tasks_for_display(self.tasks):
                self.render_task_list_item(frame, task, scroll_popup)

        for widget in (popup, area, canvas, frame):
            widget.bind("<MouseWheel>", scroll_popup)
            widget.bind("<Button-4>", scroll_popup)
            widget.bind("<Button-5>", scroll_popup)

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

    def render_task_list_item(self, parent: tk.Widget, task: Task, scroll_callback) -> None:
        task_bg = self.pinned_task_bg(task)
        row = tk.Frame(parent, bg=task_bg)
        row.pack(fill="x", pady=0)
        line = tk.Frame(row, bg=self.settings["accent"], height=1)
        line.pack(side="bottom", fill="x", padx=4)
        content = tk.Frame(row, bg=task_bg)
        content.pack(fill="x", pady=8)
        content.grid_columnconfigure(0, minsize=54)
        content.grid_columnconfigure(1, weight=1)
        content.grid_columnconfigure(2, minsize=112)
        content.grid_columnconfigure(3, minsize=52)

        visible_today = task in self.visible_tasks()
        status_text = "今日" if visible_today else "非今日"
        tk.Label(
            content,
            text=status_text,
            bg=task_bg,
            fg=self.settings["text"],
            font=self.small_font,
            width=5,
            anchor="w",
        ).grid(row=0, column=0, sticky="w", padx=(2, 8))

        tk.Label(
            content,
            text=task.text,
            bg=task_bg,
            fg=self.settings["text"],
            font=self.body_font,
            anchor="w",
        ).grid(row=0, column=1, sticky="ew", padx=(0, 8))

        repeat_button = tk.Button(
            content,
            text=self.task_list_repeat_label(task),
            bd=0,
            width=8,
            font=self.small_font,
            bg=task_bg,
            fg=self.settings["text"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )
        if self.days_until_next_interval(task) is None:
            repeat_button.configure(
                command=lambda selected=task, anchor=repeat_button: self.show_repeat_popup(
                    anchor,
                    lambda value, custom=None, selected=selected: self.update_repeat_from_list(selected, value, custom),
                )
            )
        else:
            repeat_button.configure(
                command=lambda selected=task, button=repeat_button: self.toggle_interval_label(selected, button)
            )
        repeat_button.grid(row=0, column=2, sticky="ew", padx=(0, 8))

        delete_button = tk.Button(
            content,
            text="×",
            command=lambda selected=task: self.delete_task_from_list(selected),
            bd=0,
            width=2,
            font=self.icon_font,
            bg=task_bg,
            fg=self.settings["accent"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
        )
        delete_button.grid(row=0, column=3, sticky="ew")

        for widget in row.winfo_children() + content.winfo_children() + [row, content, line, repeat_button, delete_button]:
            widget.bind("<MouseWheel>", scroll_callback)
            widget.bind("<Button-4>", scroll_callback)
            widget.bind("<Button-5>", scroll_callback)
            widget.bind("<Button-3>", lambda event, selected=task: self.show_task_context_menu(event, selected, True))

    def update_repeat_from_list(self, task: Task, repeat: str, custom: dict | None = None) -> None:
        self.update_repeat(task, repeat, custom)
        self.show_task_list_popup()

    def delete_task_from_list(self, task: Task) -> None:
        self.delete_task(task)
        self.show_task_list_popup()

    def show_task_context_menu(self, event: tk.Event, task: Task, refresh_task_list: bool = False) -> str:
        self.close_context_popup()

        popup = tk.Toplevel(self.root)
        self.context_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )
        popup.geometry(f"156x52+{event.x_root}+{event.y_root}" if refresh_task_list else f"156x104+{event.x_root}+{event.y_root}")

        def rename_selected() -> None:
            self.close_context_popup()
            self.show_rename_popup(task, event.x_root, event.y_root, refresh_task_list)

        def toggle_pin_selected() -> None:
            self.close_context_popup()
            self.toggle_task_pin(task, refresh_task_list)

        rename_button = tk.Button(
            popup,
            text="重命名",
            command=rename_selected,
            bd=0,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.row_bg,
            activeforeground=self.settings["text"],
            font=self.small_font,
        )
        popup.grid_rowconfigure(0, weight=1, uniform="context_menu")
        popup.grid_columnconfigure(0, weight=1)
        rename_button.grid(row=0, column=0, sticky="nsew", padx=2, pady=(2, 2 if refresh_task_list else 0))

        if not refresh_task_list:
            popup.grid_rowconfigure(1, weight=1, uniform="context_menu")
            pin_button = tk.Button(
                popup,
                text="取消置顶" if task.starred else "置顶",
                command=toggle_pin_selected,
                bd=0,
                bg=self.settings["background"],
                fg=self.settings["text"],
                activebackground=self.row_bg,
                activeforeground=self.settings["text"],
                font=self.small_font,
            )
            pin_button.grid(row=1, column=0, sticky="nsew", padx=2, pady=(0, 2))

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()
        return "break"

    def toggle_task_pin(self, task: Task, refresh_task_list: bool = False) -> None:
        task.starred = not task.starred
        self.save_tasks()
        self.render_tasks()
        if refresh_task_list and self.task_list_popup is not None:
            self.show_task_list_popup()

    def close_context_popup(self) -> None:
        if self.context_popup is not None and self.context_popup.winfo_exists():
            self.context_popup.destroy()
        self.context_popup = None

    def show_rename_popup(self, task: Task, x: int, y: int, refresh_task_list: bool = False) -> None:
        self.close_rename_popup(save=True)

        popup = tk.Toplevel(self.root)
        self.rename_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=2,
            highlightbackground=self.settings["text"],
        )

        name = tk.StringVar(value=task.text)
        popup.geometry(f"360x112+{x}+{y}")

        tk.Label(
            popup,
            text="重命名任务",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.body_font,
        ).pack(anchor="w", padx=14, pady=(12, 8))

        entry = tk.Entry(
            popup,
            textvariable=name,
            bd=0,
            insertbackground=self.settings["text"],
            bg=self.row_bg,
            fg=self.settings["text"],
            font=self.body_font,
            highlightthickness=1,
            highlightbackground=self.settings["text"],
            highlightcolor=self.settings["accent"],
        )
        entry.pack(fill="x", padx=14, ipady=6)

        def save_name() -> None:
            new_name = name.get().strip()
            if not new_name:
                self.close_rename_popup(save=False)
                return
            task.text = new_name
            self.save_tasks()
            self.close_rename_popup(save=False)
            self.render_tasks()
            if refresh_task_list and self.task_list_popup is not None:
                self.show_task_list_popup()

        self.rename_save_callback = save_name
        entry.bind("<Return>", lambda _event: save_name())
        entry.bind("<Escape>", lambda _event: self.close_rename_popup(save=False))
        popup.lift()
        popup.grab_set()
        entry.focus_force()
        entry.selection_range(0, "end")
        self.force_x11_focus(entry)
        popup.after(40, lambda: (entry.focus_force(), self.force_x11_focus(entry)))

    def close_rename_popup(self, *, save: bool = False) -> None:
        if save and self.rename_save_callback is not None:
            callback = self.rename_save_callback
            self.rename_save_callback = None
            callback()
            return
        self.rename_save_callback = None
        if self.rename_popup is not None and self.rename_popup.winfo_exists():
            try:
                self.rename_popup.grab_release()
            except tk.TclError:
                pass
            self.rename_popup.destroy()
        self.rename_popup = None

    def close_task_list_popup(self) -> None:
        self.close_context_popup()
        self.close_rename_popup(save=True)
        if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
            self.task_list_popup.destroy()
        self.task_list_popup = None

    def draw_progress(self) -> None:
        if not hasattr(self, "progress_canvas"):
            return

        self.progress_canvas.delete("all")
        width = max(10, self.progress_canvas.winfo_width())
        height = 8
        visible_tasks = self.visible_tasks()
        done_count = sum(1 for task in visible_tasks if task.done)
        progress = done_count / len(visible_tasks) if visible_tasks else 0
        self.progress_canvas.create_rectangle(0, 2, width, height - 2, fill=self.mix(self.settings["accent"], "#ffffff", 0.2), outline="")
        self.progress_canvas.create_rectangle(0, 2, width * progress, height - 2, fill=self.settings["done"], outline="")

    def add_task(self) -> None:
        self.create_task_with_repeat(self.new_repeat.get(), self.new_custom)

    def create_task_with_repeat(self, repeat: str, custom: dict | None = None) -> None:
        text = self.new_task.get().strip()
        if not text:
            self.focus_entry()
            return

        repeat = self.normalized_repeat(repeat)
        custom_rule = custom.copy() if repeat == "自定义" and custom else None
        self.tasks.append(Task(text=text, repeat=repeat, custom=custom_rule, created_on=date.today().isoformat()))
        self.new_task.set("")
        self.new_repeat.set("单次")
        self.new_custom = None
        self.save_tasks()
        self.render_tasks()
        self.focus_entry()

    def toggle_task(self, task: Task) -> None:
        task_was_done = task.done
        task.done = not task.done
        if task_was_done and not task.done:
            task.starred = False
        if task.repeat == "自定义" and (task.custom or {}).get("type") == "day_interval":
            if task.done:
                task.custom = task.custom or {}
                task.custom["last_done_on"] = date.today().isoformat()
            elif task_was_done and task.custom and task.custom.get("last_done_on") == date.today().isoformat():
                task.custom.pop("last_done_on", None)
        self.save_tasks()
        self.render_tasks()

    def delete_task(self, task: Task) -> None:
        self.tasks = [item for item in self.tasks if item is not task]
        self.save_tasks()
        self.render_tasks()

    def update_repeat(self, task: Task, repeat: str, custom: dict | None = None) -> None:
        task.repeat = self.normalized_repeat(repeat)
        if task.repeat == "自定义":
            task.custom = custom or task.custom or self.default_custom_repeat()
            if not task.created_on:
                task.created_on = date.today().isoformat()
        else:
            task.custom = None
        self.save_tasks()
        self.render_tasks()

    def set_new_repeat(self, repeat: str, custom: dict | None = None) -> None:
        self.new_repeat.set(self.normalized_repeat(repeat))
        self.new_custom = custom if self.new_repeat.get() == "自定义" else None

    def repeat_label(self, task: Task) -> str:
        if task.repeat != "自定义":
            return task.repeat
        custom = task.custom or {}
        if custom.get("type") == "day_interval":
            interval = custom.get("interval_days", 1)
            return f"{interval}天/次"
        if custom.get("type") == "weekdays":
            weekdays = custom.get("weekdays") or []
            labels = [WEEKDAY_LABELS[index] for index in weekdays if 0 <= int(index) < len(WEEKDAY_LABELS)]
            return "".join(labels) if labels else "自定义"
        return "自定义"

    def task_list_repeat_label(self, task: Task) -> str:
        label = self.repeat_label(task)
        days_left = self.days_until_next_interval(task)
        if days_left is None or id(task) not in self.expanded_interval_labels:
            return label
        if days_left == 0:
            return "今天"
        return f"剩{days_left}天"

    def toggle_interval_label(self, task: Task, button: tk.Button) -> None:
        task_key = id(task)
        if task_key in self.expanded_interval_labels:
            self.expanded_interval_labels.remove(task_key)
        else:
            self.expanded_interval_labels.add(task_key)
        button.configure(text=self.task_list_repeat_label(task))

    def days_until_next_interval(self, task: Task) -> int | None:
        if task.repeat != "自定义":
            return None
        custom = task.custom or {}
        if custom.get("type") != "day_interval":
            return None

        today = date.today()
        try:
            start = date.fromisoformat(custom.get("last_done_on") or custom.get("start_date") or task.created_on or today.isoformat())
        except ValueError:
            start = today

        interval = max(1, int(custom.get("interval_days", 1)))
        next_due = start + timedelta(days=interval)
        while next_due < today:
            next_due += timedelta(days=interval)
        return max(0, (next_due - today).days)

    def default_custom_repeat(self) -> dict:
        return {
            "type": "weekdays",
            "weekdays": [date.today().weekday()],
            "start_date": date.today().isoformat(),
        }

    def is_custom_due(self, task: Task, day: date) -> bool:
        custom = task.custom or self.default_custom_repeat()
        if custom.get("type") == "weekdays":
            weekdays = custom.get("weekdays") or []
            return day.weekday() in weekdays

        if custom.get("type") == "day_interval":
            try:
                start = date.fromisoformat(custom.get("last_done_on") or custom.get("start_date") or task.created_on or day.isoformat())
            except ValueError:
                start = day
            interval = max(1, int(custom.get("interval_days", 1)))
            if custom.get("last_done_on") and day == start:
                return True
            day_delta = (day - start).days
            if day_delta < interval:
                return False
            return day_delta % interval == 0

        return False

    def clear_done(self) -> None:
        self.tasks = [task for task in self.tasks if not task.done]
        self.save_tasks()
        self.render_tasks()

    def today_status(self) -> dict:
        return self.status_for_day(date.today())

    def status_for_day(self, target_day: date) -> dict:
        key = target_day.isoformat()
        status = self.daily_status.setdefault(
            key,
            {
                "at_work": False,
                "arrivals": [],
                "leaves": [],
                "sessions": [],
                "current_start": "",
                "commute": "unknown",
            },
        )
        status.setdefault("at_work", False)
        status.setdefault("arrivals", [])
        status.setdefault("leaves", [])
        status.setdefault("sessions", [])
        status.setdefault("current_start", "")
        status.setdefault("commute", "unknown")
        return status

    def toggle_checkin(self) -> None:
        status = self.today_status()
        now = datetime.now()
        timestamp = now.isoformat(timespec="minutes")
        if status.get("at_work"):
            status["at_work"] = False
            status["leaves"].append(timestamp)
            start = status.get("current_start") or (status["arrivals"][-1] if status["arrivals"] else timestamp)
            status["sessions"].append({"start": start, "end": timestamp})
            status["current_start"] = ""
        else:
            status["at_work"] = True
            status["arrivals"].append(timestamp)
            status["current_start"] = timestamp
        self.save_daily_status()
        self.update_daily_status_buttons()
        self.archive_day(date.today().isoformat(), self.visible_tasks())

    def show_commute_popup(self) -> None:
        self.close_commute_popup()
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_color_popup()
        self.close_font_popup()
        self.close_history_popup()

        popup = tk.Toplevel(self.root)
        self.commute_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )

        options = [
            ("走路", "walk"),
            ("骑车", "bike"),
        ]
        popup_width = max(116, self.commute_btn.winfo_width())
        popup_height = 12 + len(options) * 44
        x = self.commute_btn.winfo_rootx()
        y = self.commute_btn.winfo_rooty() + self.commute_btn.winfo_height() + 4
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")

        for label, value in options:
            button = tk.Button(
                popup,
                text=label,
                command=lambda selected=value: self.set_commute_mode(selected),
                bd=0,
                bg=self.settings["background"],
                fg=self.settings["text"],
                activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
                activeforeground=self.settings["text"],
                font=self.small_font,
                highlightthickness=1,
                highlightbackground=self.settings["text"],
            )
            button.pack(fill="x", padx=4, pady=(4, 0), ipady=2)

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

    def set_commute_mode(self, next_value: str) -> None:
        status = self.today_status()
        status["commute"] = next_value
        self.save_daily_status()
        self.update_daily_status_buttons()
        self.archive_day(date.today().isoformat(), self.visible_tasks())
        self.close_commute_popup()

    def close_commute_popup(self) -> None:
        if self.commute_popup is not None and self.commute_popup.winfo_exists():
            self.commute_popup.destroy()
        self.commute_popup = None

    def update_daily_status_buttons(self) -> None:
        if not hasattr(self, "checkin_btn"):
            return
        status = self.today_status()
        duration = self.work_duration_for_day(date.today())
        action = "离岗" if status.get("at_work") else "到岗"
        self.checkin_btn.configure(text=f"{action} {self.format_duration(duration)}")
        commute_labels = {
            "unknown": "通勤:",
            "walk": "通勤:走路",
            "bike": "通勤:骑车",
        }
        self.commute_btn.configure(text=commute_labels.get(status.get("commute"), "通勤:"))

    def schedule_work_timer_tick(self) -> None:
        if self.work_timer_after_id is not None:
            try:
                self.root.after_cancel(self.work_timer_after_id)
            except Exception:
                pass
        self.update_daily_status_buttons()
        self.work_timer_after_id = self.root.after(30000, self.schedule_work_timer_tick)

    def work_duration_for_day(self, target_day: date) -> int:
        status = self.status_for_day(target_day)
        total = 0
        for session in status.get("sessions", []):
            total += self.session_seconds(session.get("start"), session.get("end"), target_day)
        if status.get("at_work") and status.get("current_start"):
            total += self.session_seconds(status.get("current_start"), datetime.now().isoformat(timespec="minutes"), target_day)
        return max(0, total)

    def session_seconds(self, start_text: str | None, end_text: str | None, target_day: date) -> int:
        if not start_text or not end_text:
            return 0
        try:
            start = datetime.fromisoformat(start_text)
            end = datetime.fromisoformat(end_text)
        except ValueError:
            return 0
        day_start = datetime.combine(target_day, datetime.min.time())
        day_end = day_start + timedelta(days=1)
        start = max(start, day_start)
        end = min(end, day_end)
        if end <= start:
            return 0
        return int((end - start).total_seconds())

    def format_duration(self, seconds: int) -> str:
        hours, remainder = divmod(max(0, seconds), 3600)
        minutes = remainder // 60
        return f"{hours:02d}:{minutes:02d}"

    def daily_meta_for_day(self, target_day: date) -> dict:
        status = self.status_for_day(target_day)
        commute_labels = {
            "unknown": "未记录",
            "walk": "走路",
            "bike": "骑车",
        }
        return {
            "at_work": bool(status.get("at_work")),
            "arrivals": status.get("arrivals", []),
            "leaves": status.get("leaves", []),
            "sessions": status.get("sessions", []),
            "work_duration_seconds": self.work_duration_for_day(target_day),
            "work_duration": self.format_duration(self.work_duration_for_day(target_day)),
            "commute": status.get("commute", "unknown"),
            "commute_label": commute_labels.get(status.get("commute"), "未记录"),
        }

    def init_history_storage(self) -> None:
        HISTORY_ROOT.mkdir(exist_ok=True)
        self.organize_history_by_year()
        self.rewrite_history_jsonl(date.today())
        self.migrate_legacy_history()

    def init_history_db(self, connection: sqlite3.Connection) -> None:
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS daily_records (
                record_date TEXT PRIMARY KEY,
                completed_json TEXT NOT NULL,
                incomplete_json TEXT NOT NULL,
                completed_count INTEGER NOT NULL,
                incomplete_count INTEGER NOT NULL,
                created_at TEXT NOT NULL,
                meta_json TEXT NOT NULL DEFAULT '{}'
            )
            """
        )
        columns = {row[1] for row in connection.execute("PRAGMA table_info(daily_records)").fetchall()}
        if "meta_json" not in columns:
            connection.execute("ALTER TABLE daily_records ADD COLUMN meta_json TEXT NOT NULL DEFAULT '{}'")
        connection.commit()

    def history_month_dir(self, day: date) -> Path:
        year_dir = HISTORY_ROOT / day.strftime("%Y")
        year_dir.mkdir(parents=True, exist_ok=True)
        month_dir = year_dir / day.strftime("%Y-%m")
        month_dir.mkdir(parents=True, exist_ok=True)
        self.write_history_readme(month_dir)
        return month_dir

    def organize_history_by_year(self) -> None:
        month_pattern = re.compile(r"^\d{4}-\d{2}$")
        for item in HISTORY_ROOT.iterdir():
            if not item.is_dir() or not month_pattern.match(item.name):
                continue

            year_dir = HISTORY_ROOT / item.name[:4]
            target = year_dir / item.name
            if item.resolve() == target.resolve():
                continue

            year_dir.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                shutil.move(str(item), str(target))
                continue

            self.merge_history_month_dirs(item, target)
            shutil.rmtree(item)

    def merge_history_month_dirs(self, source: Path, target: Path) -> None:
        for child in source.iterdir():
            destination = target / child.name
            if destination.exists():
                continue
            shutil.move(str(child), str(destination))

    def history_db_file(self, day: date) -> Path:
        return self.history_month_dir(day) / MONTH_HISTORY_DB_NAME

    def history_jsonl_file(self, day: date) -> Path:
        return self.history_month_dir(day) / MONTH_HISTORY_JSONL_NAME

    def write_history_readme(self, month_dir: Path) -> None:
        readme = month_dir / MONTH_HISTORY_README_NAME
        if readme.exists():
            return

        readme.write_text(
            "\n".join(
                [
                    "每日待办历史数据",
                    "",
                    "文件说明：",
                    f"- {MONTH_HISTORY_DB_NAME}: SQLite3 数据库，每天一行记录。",
                    f"- {MONTH_HISTORY_JSONL_NAME}: JSON Lines 文本文件，一行代表一天，方便直接交给 AI 分析。",
                    "",
                    "字段说明：",
                    "- date: 日期，格式 YYYY-MM-DD。",
                    "- completed: 当天完成的任务列表。",
                    "- incomplete: 当天未完成的任务列表。",
                    "- completed_count: 完成数量。",
                    "- incomplete_count: 未完成数量。",
                    "- created_at: 写入记录的时间。",
                    "- meta: 当天附加状态，比如到岗/离岗时间、通勤方式。",
                    "",
                    "任务字段：text 为任务文字，done 为完成状态，repeat 为 单次/每天/工作日。",
                ]
            )
            + "\n",
            encoding="utf-8",
        )

    def migrate_legacy_history(self) -> None:
        if not LEGACY_HISTORY_DB_FILE.exists():
            return

        try:
            legacy = sqlite3.connect(LEGACY_HISTORY_DB_FILE)
            rows = legacy.execute(
                """
                SELECT record_date, completed_json, incomplete_json, completed_count, incomplete_count, created_at
                FROM daily_records
                ORDER BY record_date
                """
            ).fetchall()
        except sqlite3.Error:
            return
        finally:
            try:
                legacy.close()
            except Exception:
                pass

        touched_months: set[date] = set()
        for row in rows:
            try:
                record_day = date.fromisoformat(row[0])
            except ValueError:
                continue

            connection = sqlite3.connect(self.history_db_file(record_day))
            try:
                self.init_history_db(connection)
                connection.execute(
                    """
                    INSERT OR IGNORE INTO daily_records (
                        record_date,
                        completed_json,
                        incomplete_json,
                        completed_count,
                        incomplete_count,
                        created_at,
                        meta_json
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                    """,
                    (*row, "{}"),
                )
                connection.commit()
            finally:
                connection.close()
            touched_months.add(record_day.replace(day=1))

        for month in touched_months:
            self.rewrite_history_jsonl(month)

    def archive_due_days(self) -> None:
        today = date.today().isoformat()
        active_date = self.settings.get("active_date") or today
        if not self.settings.get("active_date"):
            self.settings["active_date"] = today
            self.save_settings()
            return

        if active_date >= today:
            return

        current_day = date.fromisoformat(active_date)
        today_day = date.fromisoformat(today)
        current_tasks = self.tasks

        while current_day < today_day:
            self.archive_day(current_day.isoformat(), self.tasks_for_date(current_tasks, current_day))
            next_day = current_day + timedelta(days=1)
            current_tasks = self.next_day_tasks(current_tasks, next_day)
            current_day = next_day

        self.tasks = current_tasks
        self.settings["active_date"] = today
        self.save_tasks()
        self.save_settings()

    def next_day_tasks(self, tasks: list[Task], target_date: date) -> list[Task]:
        next_tasks = []
        for task in tasks:
            if task.repeat == "每天":
                next_tasks.append(Task(text=task.text, done=False, repeat=task.repeat, starred=task.starred, created_on=task.created_on))
            elif task.repeat == "工作日":
                next_tasks.append(Task(text=task.text, done=False, repeat=task.repeat, starred=task.starred, created_on=task.created_on))
            elif task.repeat == "自定义":
                custom = task.custom.copy() if task.custom else self.default_custom_repeat()
                next_tasks.append(
                    Task(
                        text=task.text,
                        done=False,
                        repeat=task.repeat,
                        starred=task.starred,
                        custom=custom,
                        created_on=task.created_on or target_date.isoformat(),
                    )
                )
        return next_tasks

    def archive_day(self, record_date: str, tasks: list[Task]) -> None:
        record_day = date.fromisoformat(record_date)
        completed = [asdict(task) for task in tasks if task.done]
        incomplete = [asdict(task) for task in tasks if not task.done]
        created_at = datetime.now().isoformat(timespec="seconds")
        completed_json = json.dumps(completed, ensure_ascii=False)
        incomplete_json = json.dumps(incomplete, ensure_ascii=False)
        meta_json = json.dumps(self.daily_meta_for_day(record_day), ensure_ascii=False)

        connection = sqlite3.connect(self.history_db_file(record_day))
        try:
            self.init_history_db(connection)
            connection.execute(
                """
                INSERT OR REPLACE INTO daily_records (
                    record_date,
                    completed_json,
                    incomplete_json,
                    completed_count,
                    incomplete_count,
                    created_at,
                    meta_json
                )
                VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    record_date,
                    completed_json,
                    incomplete_json,
                    len(completed),
                    len(incomplete),
                    created_at,
                    meta_json,
                ),
            )
            connection.commit()
        finally:
            connection.close()
        self.rewrite_history_jsonl(record_day)

    def rewrite_history_jsonl(self, month_day: date) -> None:
        connection = sqlite3.connect(self.history_db_file(month_day))
        try:
            self.init_history_db(connection)
            rows = connection.execute(
                """
                SELECT record_date, completed_json, incomplete_json, completed_count, incomplete_count, created_at, meta_json
                FROM daily_records
                ORDER BY record_date
                """
            ).fetchall()
        finally:
            connection.close()

        with self.history_jsonl_file(month_day).open("w", encoding="utf-8") as history_file:
            for row in rows:
                record = {
                    "date": row[0],
                    "completed": json.loads(row[1]),
                    "incomplete": json.loads(row[2]),
                    "completed_count": row[3],
                    "incomplete_count": row[4],
                    "created_at": row[5],
                    "meta": json.loads(row[6] or "{}"),
                }
                history_file.write(json.dumps(record, ensure_ascii=False) + "\n")

    def open_history_directory(self) -> None:
        month_dir = self.history_month_dir(date.today())
        self.rewrite_history_jsonl(date.today())
        self.close_color_popup()
        self.close_font_popup()
        subprocess.Popen(["xdg-open", str(month_dir)])
        self.minimize_window()

    def show_history_popup(self) -> None:
        self.stop_fireworks()
        self.close_task_list_popup()
        self.close_color_popup()
        self.close_font_popup()
        self.close_commute_popup()
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_history_popup()

        popup = tk.Toplevel(self.root)
        self.history_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=2,
            highlightbackground=self.settings["text"],
        )

        popup_width = 620
        popup_height = 560
        x = self.root.winfo_rootx() + max(24, self.root.winfo_width() - popup_width - 24)
        y = self.root.winfo_rooty() + 84
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")

        top = tk.Frame(popup, bg=self.settings["background"])
        top.pack(fill="x", padx=14, pady=(12, 8))
        tk.Label(
            top,
            text="历史存档",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.body_font,
        ).pack(side="left")
        tk.Button(
            top,
            text="×",
            command=self.close_history_popup,
            bd=0,
            width=2,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.body_font,
        ).pack(side="right")
        tk.Button(
            top,
            text="打开目录",
            command=self.open_selected_history_directory,
            bd=0,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.small_font,
        ).pack(side="right", padx=(0, 8), ipadx=8, ipady=2)

        days = tk.Frame(popup, bg=self.settings["background"])
        days.pack(fill="x", padx=14, pady=(0, 10))
        today = date.today()
        recent_days = [today - timedelta(days=offset) for offset in range(6, -1, -1)]
        for index, day in enumerate(recent_days):
            days.grid_columnconfigure(index, weight=1, uniform="history_days")
            label = "今天" if day == today else ("昨天" if day == today - timedelta(days=1) else day.strftime("%m/%d"))
            button = tk.Button(
                days,
                text=f"{day.day}日\n{label}",
                command=lambda selected=day: self.select_history_day(selected),
                bd=0,
                bg=self.settings["background"],
                fg=self.settings["text"],
                activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
                activeforeground=self.settings["text"],
                font=self.small_font,
                highlightthickness=1,
                highlightbackground=self.settings["text"],
            )
            button.grid(row=0, column=index, sticky="ew", padx=3, ipady=3)

        self.history_body = tk.Frame(popup, bg=self.settings["background"])
        self.history_body.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        self.select_history_day(today)

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

    def select_history_day(self, record_day: date) -> None:
        self.history_selected_day = record_day
        self.history_completed, self.history_incomplete = self.load_history_record(record_day)
        self.render_history_editor()

    def render_history_editor(self) -> None:
        if self.history_body is None or not self.history_body.winfo_exists():
            return
        for child in self.history_body.winfo_children():
            child.destroy()

        record_day = self.history_selected_day or date.today()
        tk.Label(
            self.history_body,
            text=record_day.strftime("%Y年%m月%d日"),
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.small_font,
            anchor="w",
        ).pack(fill="x", pady=(0, 8))

        add_row = tk.Frame(self.history_body, bg=self.settings["background"], highlightthickness=1, highlightbackground=self.settings["text"])
        add_row.pack(fill="x", pady=(0, 10))
        manual_text = tk.StringVar()
        entry = tk.Entry(
            add_row,
            textvariable=manual_text,
            bd=0,
            bg=self.mix(self.settings["background"], "#ffffff", 0.08),
            fg=self.settings["text"],
            insertbackground=self.settings["accent"],
            font=self.small_font,
        )
        entry.pack(side="left", fill="x", expand=True, padx=8, pady=8, ipady=4)
        tk.Button(
            add_row,
            text="补完成",
            command=lambda: self.add_manual_history_item(manual_text, True),
            bd=0,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.small_font,
        ).pack(side="right", padx=(4, 8), ipady=4)
        tk.Button(
            add_row,
            text="补未完成",
            command=lambda: self.add_manual_history_item(manual_text, False),
            bd=0,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.small_font,
        ).pack(side="right", padx=(4, 0), ipady=4)

        lists = tk.Frame(self.history_body, bg=self.settings["background"])
        lists.pack(fill="both", expand=True)
        lists.grid_columnconfigure(0, weight=1, uniform="history_lists")
        lists.grid_columnconfigure(1, weight=1, uniform="history_lists")
        self.render_history_column(lists, "已完成", self.history_completed, True, 0)
        self.render_history_column(lists, "未完成", self.history_incomplete, False, 1)

    def render_history_column(self, parent: tk.Widget, title: str, items: list[dict], done: bool, column: int) -> None:
        frame = tk.Frame(parent, bg=self.settings["background"], highlightthickness=1, highlightbackground=self.settings["text"])
        frame.grid(row=0, column=column, sticky="nsew", padx=(0, 6) if column == 0 else (6, 0))
        tk.Label(
            frame,
            text=f"{title} {len(items)}项",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.small_font,
            anchor="w",
        ).pack(fill="x", padx=8, pady=(8, 4))

        if not items:
            tk.Label(
                frame,
                text="暂无记录",
                bg=self.settings["background"],
                fg=self.mix(self.settings["text"], self.settings["background"], 0.35),
                font=self.small_font,
            ).pack(anchor="center", pady=20)
            return

        for index, item in enumerate(items):
            row = tk.Frame(frame, bg=self.settings["background"])
            row.pack(fill="x", padx=8, pady=3)
            tk.Button(
                row,
                text="✓" if done else "○",
                command=lambda item_index=index, source_done=done: self.move_history_item(item_index, source_done),
                bd=0,
                width=2,
                bg=self.settings["background"],
                fg=self.settings["done"] if done else self.settings["accent"],
                activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
                activeforeground=self.settings["text"],
                font=self.small_font,
            ).pack(side="left")
            tk.Label(
                row,
                text=str(item.get("text", "")),
                bg=self.settings["background"],
                fg=self.settings["text"],
                font=self.small_font,
                anchor="w",
                wraplength=180,
            ).pack(side="left", fill="x", expand=True, padx=(4, 0))

    def load_history_record(self, record_day: date) -> tuple[list[dict], list[dict]]:
        connection = sqlite3.connect(self.history_db_file(record_day))
        try:
            self.init_history_db(connection)
            row = connection.execute(
                "SELECT completed_json, incomplete_json FROM daily_records WHERE record_date = ?",
                (record_day.isoformat(),),
            ).fetchone()
        finally:
            connection.close()

        if row:
            return json.loads(row[0]), json.loads(row[1])

        scheduled = []
        for task in self.tasks_for_date(self.tasks, record_day):
            item = asdict(task)
            item["done"] = False
            scheduled.append(item)
        return [], scheduled

    def save_history_record(self) -> None:
        if self.history_selected_day is None:
            return
        record_day = self.history_selected_day
        completed = [{**item, "done": True} for item in self.history_completed]
        incomplete = [{**item, "done": False} for item in self.history_incomplete]
        meta_json = json.dumps(self.daily_meta_for_day(record_day), ensure_ascii=False)
        connection = sqlite3.connect(self.history_db_file(record_day))
        try:
            self.init_history_db(connection)
            connection.execute(
                """
                INSERT OR REPLACE INTO daily_records (
                    record_date,
                    completed_json,
                    incomplete_json,
                    completed_count,
                    incomplete_count,
                    created_at,
                    meta_json
                )
                VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    record_day.isoformat(),
                    json.dumps(completed, ensure_ascii=False),
                    json.dumps(incomplete, ensure_ascii=False),
                    len(completed),
                    len(incomplete),
                    datetime.now().isoformat(timespec="seconds"),
                    meta_json,
                ),
            )
            connection.commit()
        finally:
            connection.close()
        self.rewrite_history_jsonl(record_day)

    def move_history_item(self, index: int, source_done: bool) -> None:
        source = self.history_completed if source_done else self.history_incomplete
        target = self.history_incomplete if source_done else self.history_completed
        if not 0 <= index < len(source):
            return
        item = source.pop(index)
        item["done"] = not source_done
        target.append(item)
        self.save_history_record()
        self.render_history_editor()

    def add_manual_history_item(self, text_var: tk.StringVar, done: bool) -> None:
        text = text_var.get().strip()
        if not text:
            return
        record_day = self.history_selected_day or date.today()
        item = asdict(Task(text=text, done=done, repeat="手动", created_on=record_day.isoformat()))
        if done:
            self.history_completed.append(item)
        else:
            self.history_incomplete.append(item)
        text_var.set("")
        self.save_history_record()
        self.render_history_editor()

    def open_selected_history_directory(self) -> None:
        record_day = self.history_selected_day or date.today()
        self.rewrite_history_jsonl(record_day)
        subprocess.Popen(["xdg-open", str(self.history_month_dir(record_day))])

    def close_history_popup(self) -> None:
        if self.history_popup is not None and self.history_popup.winfo_exists():
            self.history_popup.destroy()
        self.history_popup = None
        self.history_body = None

    def schedule_midnight_rollover(self) -> None:
        now = datetime.now()
        tomorrow = (now + timedelta(days=1)).date()
        next_midnight = datetime.combine(tomorrow, datetime.min.time()) + timedelta(seconds=2)
        delay_ms = max(1000, int((next_midnight - now).total_seconds() * 1000))
        self.root.after(delay_ms, self.run_midnight_rollover)

    def run_midnight_rollover(self) -> None:
        self.archive_due_days()
        self.render_tasks()
        self.schedule_midnight_rollover()


    def choose_accent_color(self) -> None:
        self.show_color_palette("accent")

    def choose_background_color(self) -> None:
        self.show_color_palette("background")

    def show_repeat_popup(self, anchor: tk.Widget, apply_callback) -> None:
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_color_popup()
        self.close_font_popup()
        self.close_commute_popup()
        self.close_history_popup()

        popup = tk.Toplevel(self.root)
        self.repeat_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )

        popup_width = max(128, anchor.winfo_width())
        option_height = 46
        popup_height = len(REPEAT_OPTIONS) * option_height + 2
        root_right = self.root.winfo_rootx() + self.root.winfo_width()
        scrollbar_width = 22
        x = min(anchor.winfo_rootx(), root_right - popup_width - scrollbar_width)
        y = anchor.winfo_rooty() + anchor.winfo_height() + 4
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")

        for index, option in enumerate(REPEAT_OPTIONS):
            if option == "自定义":
                command = lambda callback=apply_callback: self.show_custom_repeat_popup(callback)
            else:
                command = lambda value=option: self.apply_repeat_choice(value, apply_callback)
            button = tk.Button(
                popup,
                text=option,
                command=command,
                bd=0,
                anchor="center",
                bg=self.settings["background"],
                fg=self.settings["text"],
                activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
                activeforeground=self.settings["text"],
                font=self.body_font,
                highlightthickness=1,
                highlightbackground=self.settings["text"],
            )
            button.place(x=5, y=5 + index * option_height, width=popup_width - 10, height=option_height - 6)

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

    def apply_repeat_choice(self, value: str, apply_callback) -> None:
        apply_callback(value, None)
        self.close_repeat_popup()

    def close_repeat_popup(self) -> None:
        if self.repeat_popup is not None and self.repeat_popup.winfo_exists():
            self.repeat_popup.destroy()
        self.repeat_popup = None

    def show_custom_repeat_popup(self, apply_callback) -> None:
        self.close_repeat_popup()
        self.close_custom_popup()

        popup = tk.Toplevel(self.root)
        self.custom_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(
            bg=self.settings["background"],
            highlightthickness=2,
            highlightbackground=self.settings["text"],
        )

        popup_width = 380
        popup_height = 360
        x = self.root.winfo_rootx() + max(24, self.root.winfo_width() - popup_width - 24)
        y = self.root.winfo_rooty() + 96
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")

        mode = tk.StringVar(value="weekdays")
        day_interval = tk.IntVar(value=90)
        weekday_vars = [tk.BooleanVar(value=False) for _index in range(7)]
        hover = self.mix(self.settings["background"], "#ffffff", 0.12)

        top = tk.Frame(popup, bg=self.settings["background"])
        top.pack(fill="x", padx=14, pady=(12, 8))
        tk.Label(
            top,
            text="自定义重复",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.body_font,
        ).pack(side="left")
        tk.Button(
            top,
            text="×",
            command=self.close_custom_popup,
            bd=0,
            width=2,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=hover,
            activeforeground=self.settings["text"],
            font=self.body_font,
        ).pack(side="right")

        body_area = tk.Frame(popup, bg=self.settings["background"])
        body_area.pack(fill="both", expand=True, padx=16, pady=(0, 12))

        body_scrollbar = tk.Scrollbar(
            body_area,
            orient="vertical",
            bd=0,
            width=12,
            elementborderwidth=0,
            highlightthickness=0,
        )
        body_scrollbar.pack(side="right", fill="y")

        body_canvas = tk.Canvas(
            body_area,
            bd=0,
            highlightthickness=0,
            bg=self.settings["background"],
            yscrollincrement=24,
            yscrollcommand=body_scrollbar.set,
        )
        body_canvas.pack(side="left", fill="both", expand=True)
        body_scrollbar.configure(
            command=body_canvas.yview,
            bg=self.settings["text"],
            activebackground=self.settings["text"],
            troughcolor=self.mix(self.settings["background"], "#ffffff", 0.18),
        )

        body = tk.Frame(body_canvas, bg=self.settings["background"])
        body_window = body_canvas.create_window((0, 0), window=body, anchor="nw")

        def update_custom_scroll_region(_event: tk.Event | None = None) -> None:
            body_canvas.configure(scrollregion=body_canvas.bbox("all"))

        def resize_custom_body(event: tk.Event) -> None:
            body_canvas.itemconfigure(body_window, width=event.width)
            update_custom_scroll_region()

        def scroll_custom_body(event: tk.Event) -> str:
            if getattr(event, "num", None) == 4:
                body_canvas.yview_scroll(-3, "units")
            elif getattr(event, "num", None) == 5:
                body_canvas.yview_scroll(3, "units")
            else:
                direction = -1 if event.delta > 0 else 1
                body_canvas.yview_scroll(direction * 3, "units")
            return "break"

        def bind_custom_scroll(widget: tk.Widget) -> None:
            widget.bind("<MouseWheel>", scroll_custom_body)
            widget.bind("<Button-4>", scroll_custom_body)
            widget.bind("<Button-5>", scroll_custom_body)

        def bind_custom_scroll_tree(widget: tk.Widget) -> None:
            bind_custom_scroll(widget)
            for child in widget.winfo_children():
                bind_custom_scroll_tree(child)

        body.bind("<Configure>", update_custom_scroll_region)
        body_canvas.bind("<Configure>", resize_custom_body)
        bind_custom_scroll(popup)
        bind_custom_scroll(body_area)
        bind_custom_scroll(body_canvas)
        bind_custom_scroll(body)

        self.custom_radio(body, "每周指定日期", mode, "weekdays").pack(anchor="w", pady=(4, 6))
        weekdays = tk.Frame(body, bg=self.settings["background"])
        weekdays.pack(fill="x", pady=(0, 14))
        for index, label in enumerate(WEEKDAY_LABELS):
            checkbutton = tk.Checkbutton(
                weekdays,
                text=label,
                variable=weekday_vars[index],
                bg=self.settings["background"],
                fg=self.settings["text"],
                selectcolor=self.settings["background"],
                activebackground=hover,
                activeforeground=self.settings["text"],
                font=self.small_font,
            )
            checkbutton.grid(row=index // 3, column=index % 3, sticky="w", padx=(0, 16), pady=3)
            bind_custom_scroll(checkbutton)

        self.custom_radio(body, "间隔多少天执行一次", mode, "day_interval").pack(anchor="w", pady=(4, 6))
        days = tk.Frame(body, bg=self.settings["background"])
        days.pack(fill="x", pady=(0, 16))
        tk.Label(days, text="间隔", bg=self.settings["background"], fg=self.settings["text"], font=self.small_font).pack(side="left")
        interval_spin = tk.Spinbox(days, from_=1, to=9999, textvariable=day_interval, width=6, font=self.small_font)
        interval_spin.pack(side="left", padx=6)
        tk.Label(days, text="天执行一次", bg=self.settings["background"], fg=self.settings["text"], font=self.small_font).pack(side="left")
        for widget in (weekdays, days, interval_spin):
            bind_custom_scroll(widget)

        save = tk.Button(
            body,
            text="保存规则",
            command=lambda: self.save_custom_repeat(
                apply_callback,
                mode.get(),
                day_interval.get(),
                [index for index, variable in enumerate(weekday_vars) if variable.get()],
            ),
            bd=0,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=hover,
            activeforeground=self.settings["text"],
            font=self.body_font,
            highlightthickness=1,
            highlightbackground=self.settings["text"],
        )
        save.pack(fill="x", ipady=6)
        bind_custom_scroll(save)
        bind_custom_scroll_tree(body)
        update_custom_scroll_region()

        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

    def custom_radio(self, parent: tk.Widget, text: str, variable: tk.StringVar, value: str) -> tk.Radiobutton:
        return tk.Radiobutton(
            parent,
            text=text,
            variable=variable,
            value=value,
            bg=self.settings["background"],
            fg=self.settings["text"],
            selectcolor=self.settings["background"],
            activebackground=self.mix(self.settings["background"], "#ffffff", 0.12),
            activeforeground=self.settings["text"],
            font=self.small_font,
        )

    def save_custom_repeat(
        self,
        apply_callback,
        mode: str,
        interval_days: int,
        weekdays: list[int],
    ) -> None:
        if mode == "day_interval":
            custom = {
                "type": "day_interval",
                "interval_days": max(1, int(interval_days)),
                "start_date": date.today().isoformat(),
            }
        else:
            custom = {
                "type": "weekdays",
                "weekdays": weekdays or [date.today().weekday()],
                "start_date": date.today().isoformat(),
            }

        apply_callback("自定义", custom)
        self.close_custom_popup()

    def close_custom_popup(self) -> None:
        if self.custom_popup is not None and self.custom_popup.winfo_exists():
            self.custom_popup.destroy()
        self.custom_popup = None

    def show_color_palette(self, target: str) -> None:
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_font_popup()
        self.close_color_popup()
        self.close_commute_popup()
        self.close_history_popup()

        colors = ACCENT_COLORS if target == "accent" else BACKGROUND_COLORS
        title = "主题色" if target == "accent" else "背景色"
        popup = tk.Toplevel(self.root)
        self.color_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(bg=self.settings["background"], highlightthickness=2, highlightbackground=self.settings["accent"])

        popup_width = 284
        popup_height = 154
        x = self.root.winfo_x() + max(24, self.root.winfo_width() - popup_width - 24)
        y = self.root.winfo_y() + max(60, self.root.winfo_height() - popup_height - 24)
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")
        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

        top = tk.Frame(popup, bg=self.settings["background"])
        top.pack(fill="x", padx=10, pady=(8, 4))

        tk.Label(
            top,
            text=f"选择{title}",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.small_font,
        ).pack(side="left")

        tk.Button(
            top,
            text="×",
            command=self.close_color_popup,
            bd=0,
            width=2,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["accent"], "#ffffff", 0.14),
            activeforeground=self.settings["text"],
            font=self.small_font,
        ).pack(side="right")

        hint = tk.Label(
            popup,
            text="滚轮左右浏览更多颜色",
            bg=self.settings["background"],
            fg=self.mix(self.settings["text"], self.settings["background"], 0.28),
            font=self.small_font,
            anchor="w",
        )
        hint.pack(fill="x", padx=10, pady=(0, 4))

        palette_canvas = tk.Canvas(
            popup,
            height=56,
            bd=0,
            highlightthickness=0,
            bg=self.settings["background"],
        )
        palette_canvas.pack(fill="x", padx=10, pady=(0, 3))

        palette_scrollbar = tk.Scrollbar(
            popup,
            orient="horizontal",
            command=palette_canvas.xview,
            troughcolor=self.mix(self.settings["background"], "#ffffff", 0.08),
            bg=self.settings["accent"],
            activebackground=self.mix(self.settings["accent"], "#ffffff", 0.2),
            bd=0,
            highlightthickness=0,
        )
        palette_scrollbar.pack(fill="x", padx=10, pady=(0, 10))
        palette_canvas.configure(xscrollcommand=palette_scrollbar.set)

        swatches = tk.Frame(palette_canvas, bg=self.settings["background"])
        canvas_window = palette_canvas.create_window((0, 0), window=swatches, anchor="nw")

        def update_scroll_region(_event: tk.Event | None = None) -> None:
            palette_canvas.configure(scrollregion=palette_canvas.bbox("all"))

        def scroll_palette(event: tk.Event) -> str:
            if getattr(event, "num", None) == 4:
                palette_canvas.xview_scroll(-3, "units")
            elif getattr(event, "num", None) == 5:
                palette_canvas.xview_scroll(3, "units")
            else:
                direction = -1 if event.delta > 0 else 1
                palette_canvas.xview_scroll(direction * 3, "units")
            return "break"

        swatches.bind("<Configure>", update_scroll_region)
        for widget in (popup, palette_canvas, swatches):
            widget.bind("<MouseWheel>", scroll_palette)
            widget.bind("<Button-4>", scroll_palette)
            widget.bind("<Button-5>", scroll_palette)

        for color in colors:
            button = tk.Button(
                swatches,
                text="",
                command=lambda selected=color, kind=target: self.apply_selected_color(kind, selected),
                bg=color,
                activebackground=color,
                bd=0,
                highlightthickness=1,
                highlightbackground=self.settings["text"],
                width=5,
                height=2,
            )
            button.pack(side="left", padx=4, pady=2)
            button.bind("<MouseWheel>", scroll_palette)
            button.bind("<Button-4>", scroll_palette)
            button.bind("<Button-5>", scroll_palette)

    def apply_selected_color(self, target: str, color: str) -> None:
        self.settings[target] = color
        if target == "accent":
            self.settings["text"] = self.mix(color, "#ffffff", 0.72)

        self.save_settings()
        self.apply_theme()
        self.render_tasks()
        self.close_color_popup()

    def close_color_popup(self) -> None:
        if self.color_popup is not None and self.color_popup.winfo_exists():
            self.color_popup.destroy()
        self.color_popup = None

    def show_font_size_popup(self) -> None:
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_color_popup()
        self.close_font_popup()
        self.close_commute_popup()
        self.close_history_popup()

        popup = tk.Toplevel(self.root)
        self.font_popup = popup
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(bg=self.settings["background"], highlightthickness=2, highlightbackground=self.settings["accent"])

        popup_width = 328
        popup_height = 258
        x = self.root.winfo_x() + max(24, self.root.winfo_width() - popup_width - 24)
        y = self.root.winfo_y() + max(60, self.root.winfo_height() - popup_height - 24)
        popup.geometry(f"{popup_width}x{popup_height}+{x}+{y}")
        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.start_outside_watch()

        top = tk.Frame(popup, bg=self.settings["background"])
        top.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(
            top,
            text="调整字体大小",
            bg=self.settings["background"],
            fg=self.settings["text"],
            font=self.small_font,
        ).pack(side="left")
        tk.Button(
            top,
            text="×",
            command=self.close_font_popup,
            bd=0,
            width=2,
            bg=self.settings["background"],
            fg=self.settings["text"],
            activebackground=self.mix(self.settings["accent"], "#ffffff", 0.14),
            activeforeground=self.settings["text"],
            font=self.small_font,
        ).pack(side="right")

        body = tk.Frame(popup, bg=self.settings["background"])
        body.pack(fill="both", expand=True, padx=12, pady=(2, 12))

        items = [
            ("标题", "title_font_size", 16, 24),
            ("正文/任务", "body_font_size", 13, 19),
            ("小按钮/标签", "small_font_size", 10, 14),
            ("图标按钮", "icon_font_size", 16, 24),
        ]
        for label_text, key, minimum, maximum in items:
            row = tk.Frame(body, bg=self.settings["background"])
            row.pack(fill="x", pady=4)
            value_label = tk.Label(
                row,
                text=str(self.font_setting(key)),
                bg=self.settings["background"],
                fg=self.settings["text"],
                font=self.small_font,
                width=3,
                anchor="e",
            )
            value_label.pack(side="right")
            tk.Label(
                row,
                text=label_text,
                bg=self.settings["background"],
                fg=self.settings["text"],
                font=self.small_font,
                width=9,
                anchor="w",
            ).pack(side="left")
            scale = tk.Scale(
                row,
                from_=minimum,
                to=maximum,
                orient="horizontal",
                showvalue=False,
                bd=0,
                highlightthickness=0,
                troughcolor=self.mix(self.settings["background"], "#ffffff", 0.14),
                bg=self.settings["background"],
                fg=self.settings["text"],
                activebackground=self.settings["accent"],
                length=170,
                command=lambda value, setting_key=key, output=value_label: self.update_font_size(setting_key, value, output),
            )
            scale.set(self.font_setting(key))
            scale.pack(side="left", fill="x", expand=True, padx=(8, 8))

    def update_font_size(self, key: str, value: str, value_label: tk.Label | None = None) -> None:
        try:
            size = int(float(value))
        except ValueError:
            return
        self.settings[key] = size
        if value_label is not None and value_label.winfo_exists():
            value_label.configure(text=str(size))
        self.apply_font_settings()
        self.save_settings()
        self.render_tasks()

    def apply_font_settings(self) -> None:
        self.title_font.configure(size=-self.font_setting("title_font_size"))
        self.body_font.configure(size=-self.font_setting("body_font_size"))
        self.small_font.configure(size=-self.font_setting("small_font_size"))
        self.icon_font.configure(size=-self.font_setting("icon_font_size"))

    def make_font(self, key: str, *, overstrike: bool = False) -> font.Font:
        return font.Font(
            family="Noto Sans CJK SC",
            size=-self.font_setting(key),
            weight="bold",
            overstrike=overstrike,
        )

    def font_setting(self, key: str) -> int:
        default = int(DEFAULT_SETTINGS[key])
        limits = {
            "title_font_size": (16, 24),
            "body_font_size": (13, 19),
            "small_font_size": (10, 14),
            "icon_font_size": (16, 24),
        }
        try:
            size = int(self.settings.get(key, default))
        except (TypeError, ValueError):
            return default
        minimum, maximum = limits.get(key, (7, 28))
        return max(minimum, min(maximum, size))

    def close_font_popup(self) -> None:
        if self.font_popup is not None and self.font_popup.winfo_exists():
            self.font_popup.destroy()
        self.font_popup = None

    def toggle_topmost(self) -> None:
        self.root.attributes("-topmost", self.always_on_top.get())

    def init_x11(self) -> tuple[object, c_void_p, int] | None:
        try:
            x11 = cdll.LoadLibrary("libX11.so.6")
            x11.XOpenDisplay.argtypes = [c_void_p]
            x11.XOpenDisplay.restype = c_void_p
            x11.XDefaultRootWindow.argtypes = [c_void_p]
            x11.XDefaultRootWindow.restype = c_ulong
            x11.XQueryPointer.argtypes = [
                c_void_p,
                c_ulong,
                c_void_p,
                c_void_p,
                c_void_p,
                c_void_p,
                c_void_p,
                c_void_p,
                c_void_p,
            ]
            x11.XQueryPointer.restype = c_int
            x11.XSetInputFocus.argtypes = [c_void_p, c_ulong, c_int, c_ulong]
            x11.XSetInputFocus.restype = c_int
            x11.XFlush.argtypes = [c_void_p]
            x11.XFlush.restype = c_int
            display = x11.XOpenDisplay(None)
            if not display:
                return None
            root_window = x11.XDefaultRootWindow(display)
            return x11, display, root_window
        except Exception:
            return None

    def force_x11_focus(self, widget: tk.Widget) -> None:
        if self.x11 is None:
            return
        try:
            widget.update_idletasks()
            x11, display, _root_window = self.x11
            x11.XSetInputFocus(display, c_ulong(widget.winfo_id()), REVERT_TO_PARENT, CURRENT_TIME)
            x11.XFlush(display)
        except Exception:
            pass

    def pointer_state(self) -> tuple[int, int, int]:
        if self.x11 is None:
            return (
                self.root.winfo_pointerx(),
                self.root.winfo_pointery(),
                0,
            )

        x11, display, root_window = self.x11
        root_return = c_ulong()
        child_return = c_ulong()
        root_x = c_int()
        root_y = c_int()
        win_x = c_int()
        win_y = c_int()
        mask = c_uint()
        ok = x11.XQueryPointer(
            display,
            root_window,
            byref(root_return),
            byref(child_return),
            byref(root_x),
            byref(root_y),
            byref(win_x),
            byref(win_y),
            byref(mask),
        )
        if not ok:
            return (
                self.root.winfo_pointerx(),
                self.root.winfo_pointery(),
                0,
            )

        return root_x.value, root_y.value, mask.value & BUTTON_MASKS

    def force_close(self) -> None:
        try:
            self.close_color_popup()
            self.close_font_popup()
            self.close_commute_popup()
            self.close_repeat_popup()
            self.close_custom_popup()
            self.close_context_popup()
            self.close_rename_popup(save=True)
            self.close_task_list_popup()
            self.close_history_popup()
        except Exception:
            pass
        try:
            if self.status_icon is not None:
                self.status_icon.set_visible(False)
            Gtk.main_quit()
        except Exception:
            pass
        try:
            self.root.quit()
            self.root.destroy()
        finally:
            os._exit(0)

    def minimize_window(self) -> None:
        self.cancel_outside_watch()
        self.disable_task_mousewheel()
        self.close_color_popup()
        self.close_font_popup()
        self.close_commute_popup()
        self.close_repeat_popup()
        self.close_custom_popup()
        self.close_context_popup()
        self.close_rename_popup(save=True)
        self.close_task_list_popup()
        self.close_history_popup()
        self.window_locked = False
        self.root.withdraw()

    def setup_status_icon(self) -> None:
        self.status_icon = Gtk.StatusIcon.new_from_file(str(TRAY_ICON_FILE))
        self.status_icon.set_tooltip_text("今日待办")
        self.status_icon.set_visible(True)
        self.status_icon.connect("activate", self.on_status_icon_activate)
        self.status_icon.connect("popup-menu", self.on_status_icon_menu)

        menu = Gtk.Menu()
        show_item = Gtk.MenuItem(label="显示/隐藏今日待办")
        show_item.connect("activate", lambda _item: self.root.after(0, self.toggle_window_from_status_icon))
        menu.append(show_item)
        menu.append(Gtk.SeparatorMenuItem())
        quit_item = Gtk.MenuItem(label="退出")
        quit_item.connect("activate", lambda _item: self.root.after(0, self.force_close))
        menu.append(quit_item)
        menu.show_all()
        self.status_menu = menu

        self.gtk_thread = threading.Thread(target=Gtk.main, daemon=True)
        self.gtk_thread.start()

    def on_status_icon_activate(self, _icon: Gtk.StatusIcon) -> None:
        self.root.after(0, self.toggle_window_from_status_icon)

    def on_status_icon_menu(self, icon: Gtk.StatusIcon, button: int, activate_time: int) -> None:
        if self.status_menu is not None:
            self.status_menu.popup(None, None, Gtk.StatusIcon.position_menu, icon, button, activate_time)

    def toggle_window_from_status_icon(self) -> None:
        if self.root.state() == "withdrawn":
            self.show_plan_window()
        else:
            self.minimize_window()

    def show_plan_window(self) -> None:
        self.cancel_auto_hide()
        self.window_locked = False
        self.place_top_right()
        self.root.overrideredirect(True)
        self.root.deiconify()
        self.root.attributes("-topmost", True)
        self.root.lift()
        self.root.after(30, self.claim_window_focus)
        _pointer_x, _pointer_y, buttons = self.pointer_state()
        self.last_pointer_buttons = buttons
        self.enable_task_mousewheel()
        self.start_outside_watch()

    def claim_window_focus(self) -> None:
        if self.root.state() == "withdrawn":
            return
        self.root.lift()
        self.root.focus_force()
        self.force_x11_focus(self.root)
        self.root.overrideredirect(True)

    def focus_entry(self, _event: tk.Event | None = None) -> None:
        self.root.focus_force()
        self.entry.focus_force()
        self.force_x11_focus(self.entry)
        self.root.after(20, lambda: (self.entry.focus_force(), self.force_x11_focus(self.entry)))

    def focus_clicked_widget(self, event: tk.Event) -> None:
        try:
            if event.widget.winfo_toplevel() is self.root:
                if event.widget is self.entry:
                    self.focus_entry()
                    return
                self.root.focus_force()
        except tk.TclError:
            pass

    def cancel_auto_hide(self, _event: tk.Event | None = None) -> None:
        if self.hide_after_id is not None:
            self.root.after_cancel(self.hide_after_id)
            self.hide_after_id = None

    def cancel_outside_watch(self) -> None:
        if self.outside_watch_id is not None:
            self.root.after_cancel(self.outside_watch_id)
            self.outside_watch_id = None

    def maybe_hide_preview(self, _event: tk.Event | None = None) -> None:
        self.cancel_auto_hide()
        self.hide_after_id = self.root.after(260, self.hide_preview_if_idle)

    def hide_preview_if_idle(self) -> None:
        self.hide_after_id = None
        if self.window_locked:
            return

        pointer_x = self.root.winfo_pointerx()
        pointer_y = self.root.winfo_pointery()
        if self.pointer_inside_window(self.root, pointer_x, pointer_y):
            return

        self.root.withdraw()

    def hide_after_external_click(self, _event: tk.Event | None = None) -> None:
        if self.color_popup is not None and self.color_popup.winfo_exists():
            return
        if self.font_popup is not None and self.font_popup.winfo_exists():
            return
        if self.commute_popup is not None and self.commute_popup.winfo_exists():
            return
        if self.repeat_popup is not None and self.repeat_popup.winfo_exists():
            return
        if self.custom_popup is not None and self.custom_popup.winfo_exists():
            return
        if self.context_popup is not None and self.context_popup.winfo_exists():
            return
        if self.rename_popup is not None and self.rename_popup.winfo_exists():
            return
        if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
            return
        if self.history_popup is not None and self.history_popup.winfo_exists():
            return
        self.root.after(80, self.hide_if_pointer_outside)

    def hide_if_pointer_outside(self) -> None:
        if self.root.state() == "withdrawn":
            return
        if self.color_popup is not None and self.color_popup.winfo_exists():
            return
        if self.font_popup is not None and self.font_popup.winfo_exists():
            return
        if self.commute_popup is not None and self.commute_popup.winfo_exists():
            return
        if self.repeat_popup is not None and self.repeat_popup.winfo_exists():
            return
        if self.custom_popup is not None and self.custom_popup.winfo_exists():
            return
        if self.context_popup is not None and self.context_popup.winfo_exists():
            return
        if self.rename_popup is not None and self.rename_popup.winfo_exists():
            return
        if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
            return
        if self.history_popup is not None and self.history_popup.winfo_exists():
            return

        pointer_x = self.root.winfo_pointerx()
        pointer_y = self.root.winfo_pointery()
        if self.pointer_inside_window(self.root, pointer_x, pointer_y):
            return

        self.minimize_window()

    def start_outside_watch(self) -> None:
        if self.outside_watch_id is not None:
            self.root.after_cancel(self.outside_watch_id)
        self.outside_watch_id = self.root.after(80, self.watch_for_outside_click)

    def watch_for_outside_click(self) -> None:
        self.outside_watch_id = None
        if self.root.state() == "withdrawn":
            return

        pointer_x, pointer_y, buttons = self.pointer_state()
        outside_click_started = buttons and not self.last_pointer_buttons
        self.last_pointer_buttons = buttons

        if not outside_click_started:
            self.start_outside_watch()
            return

        if self.color_popup is not None and self.color_popup.winfo_exists():
            if self.pointer_inside_window(self.color_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_color_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.font_popup is not None and self.font_popup.winfo_exists():
            if self.pointer_inside_window(self.font_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_font_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.commute_popup is not None and self.commute_popup.winfo_exists():
            if self.pointer_inside_window(self.commute_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_commute_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.repeat_popup is not None and self.repeat_popup.winfo_exists():
            if self.pointer_inside_window(self.repeat_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_repeat_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.custom_popup is not None and self.custom_popup.winfo_exists():
            if self.pointer_inside_window(self.custom_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_custom_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.context_popup is not None and self.context_popup.winfo_exists():
            if self.pointer_inside_window(self.context_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_context_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
                if self.pointer_inside_window(self.task_list_popup, pointer_x, pointer_y):
                    self.start_outside_watch()
                    return

        if self.rename_popup is not None and self.rename_popup.winfo_exists():
            if self.pointer_inside_window(self.rename_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_rename_popup(save=True)
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
                if self.pointer_inside_window(self.task_list_popup, pointer_x, pointer_y):
                    self.start_outside_watch()
                    return

        if self.task_list_popup is not None and self.task_list_popup.winfo_exists():
            if self.pointer_inside_window(self.task_list_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_task_list_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.history_popup is not None and self.history_popup.winfo_exists():
            if self.pointer_inside_window(self.history_popup, pointer_x, pointer_y):
                self.start_outside_watch()
                return
            self.close_history_popup()
            if self.pointer_inside_window(self.root, pointer_x, pointer_y):
                self.start_outside_watch()
                return

        if self.pointer_inside_window(self.root, pointer_x, pointer_y):
            self.start_outside_watch()
            return

        self.minimize_window()

    def lock_window_for_editing(self, event: tk.Event) -> None:
        try:
            if event.widget.winfo_toplevel() is self.root:
                self.window_locked = True
                self.cancel_auto_hide()
        except tk.TclError:
            pass

    def pointer_inside_window(self, window: tk.Toplevel | tk.Tk, pointer_x: int, pointer_y: int) -> bool:
        x = window.winfo_rootx()
        y = window.winfo_rooty()
        return x <= pointer_x <= x + window.winfo_width() and y <= pointer_y <= y + window.winfo_height()

    def restore_borderless(self, _event: tk.Event) -> None:
        if self.root.state() == "normal":
            self.root.after(10, lambda: self.root.overrideredirect(True))

    def resize_task_window(self, event: tk.Event) -> None:
        self.task_canvas.itemconfigure(self.task_window, width=event.width)
        self.update_task_scroll_region()

    def update_task_scroll_region(self, _event: tk.Event | None = None) -> None:
        self.task_canvas.configure(scrollregion=self.task_canvas.bbox("all"))

    def task_canvas_scroll(self, *args: str) -> None:
        self.task_canvas.yview(*args)

    def bind_task_scroll_widget(self, widget: tk.Widget) -> None:
        widget.bind("<MouseWheel>", self.on_task_mousewheel)
        widget.bind("<Button-4>", self.on_task_mousewheel)
        widget.bind("<Button-5>", self.on_task_mousewheel)

    def enable_task_mousewheel(self, _event: tk.Event | None = None) -> None:
        self.root.bind_all("<MouseWheel>", self.on_task_mousewheel)
        self.root.bind_all("<Button-4>", self.on_task_mousewheel)
        self.root.bind_all("<Button-5>", self.on_task_mousewheel)

    def disable_task_mousewheel(self, _event: tk.Event | None = None) -> None:
        self.root.unbind_all("<MouseWheel>")
        self.root.unbind_all("<Button-4>")
        self.root.unbind_all("<Button-5>")

    def on_task_mousewheel(self, event: tk.Event) -> str:
        if self.root.state() == "withdrawn":
            return "break"
        pointer_x = self.root.winfo_pointerx()
        pointer_y = self.root.winfo_pointery()
        if not self.pointer_inside_window(self.task_area, pointer_x, pointer_y):
            return ""
        if getattr(event, "num", None) == 4:
            self.task_canvas.yview_scroll(-3, "units")
        elif getattr(event, "num", None) == 5:
            self.task_canvas.yview_scroll(3, "units")
        else:
            direction = -1 if event.delta > 0 else 1
            self.task_canvas.yview_scroll(direction * 3, "units")
        return "break"

    def start_drag(self, event: tk.Event) -> None:
        self.drag_start_x = event.x
        self.drag_start_y = event.y

    def drag_window(self, event: tk.Event) -> None:
        x = self.root.winfo_x() + event.x - self.drag_start_x
        y = self.root.winfo_y() + event.y - self.drag_start_y
        self.root.geometry(f"+{x}+{y}")

    def start_resize(self, event: tk.Event, mode: str = "corner") -> None:
        self.resize_start_x = event.x_root
        self.resize_start_y = event.y_root
        self.resize_start_width = self.root.winfo_width()
        self.resize_start_height = self.root.winfo_height()
        self.resize_start_root_x = self.root.winfo_x()
        self.resize_start_root_y = self.root.winfo_y()
        self.resize_mode = mode

    def resize_window(self, event: tk.Event) -> None:
        width = self.resize_start_width
        height = self.resize_start_height

        if self.resize_mode in {"right", "corner"}:
            width = max(MIN_WINDOW_WIDTH, self.resize_start_width + event.x_root - self.resize_start_x)
        if self.resize_mode in {"bottom", "corner"}:
            height = max(MIN_WINDOW_HEIGHT, self.resize_start_height + event.y_root - self.resize_start_y)

        self.root.geometry(f"{width}x{height}+{self.resize_start_root_x}+{self.resize_start_root_y}")

    def normalized_repeat(self, repeat: str) -> str:
        if repeat in REPEAT_OPTIONS:
            return repeat
        return "单次"

    def normalized_custom(self, custom: object) -> dict | None:
        if not isinstance(custom, dict):
            return None
        if custom.get("type") == "day_interval":
            return {
                "type": "day_interval",
                "interval_days": max(1, int(custom.get("interval_days", 1))),
                "start_date": str(custom.get("start_date") or date.today().isoformat()),
            }
        if custom.get("type") == "monthly_interval":
            interval_months = max(1, int(custom.get("interval_months", 1)))
            return {
                "type": "day_interval",
                "interval_days": interval_months * 30,
                "start_date": str(custom.get("start_date") or date.today().isoformat()),
            }
        if custom.get("type") == "weekdays":
            weekdays = [int(day) for day in custom.get("weekdays", []) if 0 <= int(day) <= 6]
            return {
                "type": "weekdays",
                "weekdays": weekdays or [date.today().weekday()],
                "start_date": str(custom.get("start_date") or date.today().isoformat()),
            }
        return None

    def load_tasks(self) -> list[Task]:
        if not DATA_FILE.exists():
            return [
                Task("完成工作报告", True, "单次", False),
                Task("发邮件给客户", True, "单次", True),
                Task("去健身房锻炼", False, "每天", True),
                Task("阅读30分钟书籍", False, "工作日", True),
            ]

        try:
            raw_tasks = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return []

        tasks = []
        for item in raw_tasks:
            if not item.get("text"):
                continue
            tasks.append(
                Task(
                    text=item["text"],
                    done=item.get("done", False),
                    repeat=self.normalized_repeat(item.get("repeat", "单次")),
                    starred=item.get("starred", False),
                    custom=self.normalized_custom(item.get("custom")),
                    created_on=item.get("created_on", ""),
                )
            )
        return tasks

    def save_tasks(self) -> None:
        data = [asdict(task) for task in self.tasks]
        DATA_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    def load_daily_status(self) -> dict:
        if not DAILY_STATUS_FILE.exists():
            return {}
        try:
            data = json.loads(DAILY_STATUS_FILE.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return {}
        return data if isinstance(data, dict) else {}

    def save_daily_status(self) -> None:
        DAILY_STATUS_FILE.write_text(json.dumps(self.daily_status, ensure_ascii=False, indent=2), encoding="utf-8")

    def load_settings(self) -> dict[str, str]:
        if not SETTINGS_FILE.exists():
            return DEFAULT_SETTINGS.copy()

        try:
            saved = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return DEFAULT_SETTINGS.copy()

        return {**DEFAULT_SETTINGS, **saved}

    def save_settings(self) -> None:
        SETTINGS_FILE.write_text(json.dumps(self.settings, ensure_ascii=False, indent=2), encoding="utf-8")

    def mix(self, color_a: str, color_b: str, ratio: float) -> str:
        ratio = max(0, min(1, ratio))
        first = self.hex_to_rgb(color_a)
        second = self.hex_to_rgb(color_b)
        mixed = tuple(round(a * (1 - ratio) + b * ratio) for a, b in zip(first, second))
        return "#%02x%02x%02x" % mixed

    def hex_to_rgb(self, color: str) -> tuple[int, int, int]:
        color = color.lstrip("#")
        if len(color) != 6:
            color = "000000"
        return tuple(int(color[index : index + 2], 16) for index in (0, 2, 4))

    def run(self) -> None:
        self.root.mainloop()


if __name__ == "__main__":
    DesktopTodo().run()
