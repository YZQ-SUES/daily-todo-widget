# 今日待办桌面小窗

一个 Linux 桌面端待办小工具：程序常驻右上角状态栏，点击小图标显示今日待办窗口。主窗口只显示今天该做的任务，全部任务可以在「任务列表」里统一管理。

## 功能

- 状态栏小图标常驻后台，点击显示或隐藏窗口
- 主窗口固定显示在主显示器右上角
- 支持窗口拖动和右下角调整大小
- 支持背景颜色、字体颜色自定义
- 支持任务频率：单次、每天、工作日、自定义
- 自定义频率支持每周指定日期、间隔 N 天执行一次
- 今日待办只显示今天该出现的任务
- 任务列表显示全部已创建任务
- 每天零点自动归档当天完成和未完成事项
- 历史记录按年份和月份保存，方便交给 AI 分析

## 运行

```bash
./launch.sh
```

或者：

```bash
python3 desktop_todo.py
```

## 依赖

- Python 3
- Tkinter
- PyGObject / GTK 3
- X11 桌面环境

Ubuntu 上如果缺少依赖，可以尝试：

```bash
sudo apt install python3-tk python3-gi gir1.2-gtk-3.0
```

## 数据文件

这些文件是本机个人数据，默认不会提交到 Git：

- `tasks.json`：当前任务
- `settings.json`：主题和状态设置
- `history/YYYY/YYYY-MM/`：每日历史归档
- `daily_history.sqlite3`、`daily_history.jsonl`：旧版历史文件

历史目录中每个月会有：

- `daily_records.sqlite3`：SQLite3 数据库
- `daily_records.jsonl`：AI 友好的 JSON Lines 文本
- `README.txt`：字段说明

## 开机自启动

可以创建一个本机 `.desktop` 文件放到：

```bash
~/.config/autostart/
```

其中 `Exec` 指向本项目里的 `launch.sh`，`Icon` 指向 `assets/tray_icon.png`。
