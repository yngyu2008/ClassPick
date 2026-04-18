import json
import os
import sys
import random
import ctypes
import re
import sqlite3
import tkinter as tk
from collections import defaultdict, deque
from datetime import datetime
from tkinter import messagebox

try:
    from PIL import Image, ImageDraw, ImageFont
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False


class SeatingProgram:
    APP_DIR_NAME = "ClassPick"
    DB_FILE = "class_pick.db"

    LEGACY_DATA_FILES = [
        "class_pick_data.json",
        "class_seating_data.json",
    ]
    LEGACY_STATE_FILES = [
        "class_pick_state.json",
        "app_state.json",
    ]

    MAX_ROWS = 5
    SUPPORTED_LAYOUT_COLS = (5, 6)
    DEFAULT_LAYOUT_COLS = 6

    SEAT_WIDTH = 110
    SEAT_HEIGHT = 58
    PAIR_INNER_GAP = 8
    PAIR_OUTER_GAP = 42
    NORMAL_GAP = 22
    ROW_GAP = 18

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("클래스픽")
        self.root.configure(bg="#dff3ff")
        self.root.resizable(True, True)

        self.runtime_dir = self.get_runtime_dir()
        self.storage_dir = self.get_storage_dir()
        self.db_path = os.path.join(self.storage_dir, self.DB_FILE)

        self.init_database()
        self.migrate_json_to_db_if_needed()

        self.data = self.load_all_data()
        self.app_state = self.load_app_state()

        self.current_grade = ""
        self.current_class = ""
        self.current_layout_cols = self.DEFAULT_LAYOUT_COLS
        self.pair_mode = "짝 있음"

        self.students = []
        self.seat_map = {}
        self.selected_seat = None

        self.animating = False
        self.animation_job = None
        self.final_shuffle_result = None
        self.resize_after_id = None

        self.seat_widgets = {}

        self.build_ui()

        self.root.update_idletasks()
        self.set_main_window_geometry()

        self.root.bind("<Configure>", self.on_window_configure)
        self.root.bind("<F11>", self.toggle_fullscreen)
        self.root.bind("<Escape>", self.exit_fullscreen)

        self.restore_last_opened_class()
        self.redraw_seats()

    # ----------------------------
    # 유틸
    # ----------------------------
    def validate_numeric_input(self, value: str):
        return value.isdigit() or value == ""

    def class_key(self, grade, class_no):
        return f"{grade}-{class_no}"

    def pos_key(self, pos):
        return f"{pos[0]}_{pos[1]}"

    def extract_student_name(self, raw_text):
        text = str(raw_text).strip()
        if not text:
            return ""

        if re.match(r"^\d+\.\s*$", text):
            return ""

        match = re.match(r"^\d+\.\s*(.+)$", text)
        if match:
            return match.group(1).strip()

        return text

    def normalize_students_list(self, students):
        names = []

        for student in students:
            name = self.extract_student_name(student)
            if name:
                names.append(name)

        return [f"{index:02d}. {name}" for index, name in enumerate(names, start=1)]

    def parse_students_text(self, raw_text: str):
        lines = [line.strip() for line in raw_text.splitlines() if line.strip()]
        return self.normalize_students_list(lines)

    def validate_student_input(self, raw_text: str):
        lines = [line.strip() for line in raw_text.splitlines() if line.strip()]

        if not lines:
            return False, "학생 명단을 입력해 주세요."

        for idx, line in enumerate(lines, start=1):
            name = self.extract_student_name(line)
            if not name:
                return False, f"{idx}번째 줄에 이름이 없습니다."

        return True, ""

    def normalize_layout_cols(self, layout_cols):
        try:
            value = int(layout_cols)
        except (TypeError, ValueError):
            value = self.DEFAULT_LAYOUT_COLS

        return value if value in self.SUPPORTED_LAYOUT_COLS else self.DEFAULT_LAYOUT_COLS

    def get_max_seats(self, layout_cols=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )
        return self.MAX_ROWS * cols

    def get_effective_pair_mode(self, layout_cols=None, pair_mode=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )
        raw_pair_mode = self.pair_mode if pair_mode is None else pair_mode

        if cols == 6 and raw_pair_mode == "짝 있음":
            return "짝 있음"
        return "짝 없음"

    def build_column_positions(
        self,
        cols,
        start_x,
        seat_width,
        pair_mode,
        pair_inner_gap,
        pair_outer_gap,
        normal_gap,
    ):
        positions = []
        x = start_x

        for c in range(cols):
            positions.append(x)

            if c == cols - 1:
                continue

            if cols == 6 and pair_mode == "짝 있음":
                gap = pair_inner_gap if c % 2 == 0 else pair_outer_gap
            else:
                gap = normal_gap

            x += seat_width + gap

        return positions

    def get_total_layout_width(
        self,
        cols,
        seat_width,
        pair_mode,
        pair_inner_gap,
        pair_outer_gap,
        normal_gap,
    ):
        x_positions = self.build_column_positions(
            cols,
            0,
            seat_width,
            pair_mode,
            pair_inner_gap,
            pair_outer_gap,
            normal_gap,
        )

        if not x_positions:
            return 0

        return x_positions[-1] + seat_width

    def get_ordered_position_keys(self, layout_cols=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )

        return [
            self.pos_key((r, c))
            for r in range(self.MAX_ROWS)
            for c in range(cols)
        ]

    def remap_loaded_seat_map(self, seat_map, original_students, normalized_students):
        label_queues = defaultdict(deque)
        name_queues = defaultdict(deque)

        for old_label, new_label in zip(original_students, normalized_students):
            old_label = str(old_label).strip()
            old_name = self.extract_student_name(old_label)

            label_queues[old_label].append(new_label)
            name_queues[old_name].append(new_label)

        remapped = {}

        for key, value in seat_map.items():
            old_student = str(value.get("student", "")).strip()
            mapped_student = ""

            if old_student:
                if label_queues[old_student]:
                    mapped_student = label_queues[old_student].popleft()
                else:
                    old_name = self.extract_student_name(old_student)
                    if name_queues[old_name]:
                        mapped_student = name_queues[old_name].popleft()

            remapped[key] = {
                "student": mapped_student,
                "locked": bool(value.get("locked", False))
            }

        return remapped

    def upgrade_loaded_class_data(self, loaded):
        if not loaded:
            return None, False

        original_students = [
            str(student).strip()
            for student in loaded.get("students", [])
            if str(student).strip()
        ]
        normalized_students = self.normalize_students_list(original_students)

        original_seat_map = loaded.get("seat_map", {})
        remapped_seat_map = self.remap_loaded_seat_map(
            original_seat_map,
            original_students,
            normalized_students
        )

        layout_cols = self.normalize_layout_cols(loaded.get("layout_cols", self.DEFAULT_LAYOUT_COLS))
        pair_mode = self.get_effective_pair_mode(
            layout_cols,
            loaded.get("pair_mode", "짝 있음")
        )

        upgraded = {
            "grade": str(loaded.get("grade", "")),
            "class": str(loaded.get("class", "")),
            "layout_cols": layout_cols,
            "pair_mode": pair_mode,
            "students": normalized_students,
            "seat_map": remapped_seat_map
        }

        changed = (
            upgraded["students"] != loaded.get("students", [])
            or upgraded["seat_map"] != original_seat_map
            or upgraded["grade"] != str(loaded.get("grade", ""))
            or upgraded["class"] != str(loaded.get("class", ""))
            or upgraded["layout_cols"] != self.normalize_layout_cols(
                loaded.get("layout_cols", self.DEFAULT_LAYOUT_COLS)
            )
            or upgraded["pair_mode"] != loaded.get("pair_mode", "짝 있음")
        )

        return upgraded, changed

    def get_work_area(self):
        if os.name == "nt":
            try:
                SPI_GETWORKAREA = 48

                class RECT(ctypes.Structure):
                    _fields_ = [
                        ("left", ctypes.c_long),
                        ("top", ctypes.c_long),
                        ("right", ctypes.c_long),
                        ("bottom", ctypes.c_long),
                    ]

                rect = RECT()
                ctypes.windll.user32.SystemParametersInfoW(
                    SPI_GETWORKAREA, 0, ctypes.byref(rect), 0
                )
                return rect.left, rect.top, rect.right, rect.bottom
            except Exception:
                pass

        return 0, 0, self.root.winfo_screenwidth(), self.root.winfo_screenheight()

    def center_window_in_work_area(self, window, width, height):
        left, top, right, bottom = self.get_work_area()
        area_width = right - left
        area_height = bottom - top

        width = min(width, area_width)
        height = min(height, area_height)

        x = left + max((area_width - width) // 2, 0)
        y = top + max((area_height - height) // 2, 0)

        window.geometry(f"{width}x{height}+{x}+{y}")

    def set_main_window_geometry(self):
        desired_width = 980
        desired_height = 700

        left, top, right, bottom = self.get_work_area()
        area_width = right - left
        area_height = bottom - top

        width = min(desired_width, max(area_width - 40, 900))
        height = min(desired_height, max(area_height - 40, 650))

        width = min(width, area_width)
        height = min(height, area_height)

        self.root.minsize(min(900, area_width), min(650, area_height))
        self.center_window_in_work_area(self.root, width, height)

    def on_window_configure(self, event):
        if event.widget is not self.root:
            return

        if self.resize_after_id:
            self.root.after_cancel(self.resize_after_id)

        self.resize_after_id = self.root.after(80, self.redraw_seats)

    def toggle_fullscreen(self, event=None):
        current = bool(self.root.attributes("-fullscreen"))
        self.root.attributes("-fullscreen", not current)
        self.redraw_seats()

    def exit_fullscreen(self, event=None):
        if self.root.attributes("-fullscreen"):
            self.root.attributes("-fullscreen", False)
            self.redraw_seats()

    # ----------------------------
    # 데이터 처리
    # ----------------------------
    def get_runtime_dir(self):
        if getattr(sys, "frozen", False):
            return os.path.dirname(sys.executable)
        return os.path.dirname(os.path.abspath(__file__))

    def get_storage_dir(self):
        local_app_data = os.environ.get("LOCALAPPDATA")
        if local_app_data:
            base_dir = local_app_data
        else:
            base_dir = os.path.expanduser("~")

        storage_dir = os.path.join(base_dir, self.APP_DIR_NAME)
        os.makedirs(storage_dir, exist_ok=True)
        return storage_dir

    def get_desktop_path(self):
        if os.name == "nt":
            try:
                buf = ctypes.create_unicode_buffer(260)
                CSIDL_DESKTOPDIRECTORY = 0x0010
                SHGFP_TYPE_CURRENT = 0

                result = ctypes.windll.shell32.SHGetFolderPathW(
                    None,
                    CSIDL_DESKTOPDIRECTORY,
                    None,
                    SHGFP_TYPE_CURRENT,
                    buf
                )

                if result == 0 and buf.value and os.path.isdir(buf.value):
                    return buf.value
            except Exception:
                pass

        candidates = [
            os.path.join(os.path.expanduser("~"), "Desktop"),
            os.path.join(os.path.expanduser("~"), "OneDrive", "Desktop"),
        ]

        for path in candidates:
            if os.path.isdir(path):
                return path

        return os.path.expanduser("~")

    def get_db_connection(self):
        return sqlite3.connect(self.db_path)

    def load_json_file(self, path):
        if not os.path.exists(path):
            return {}

        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    def init_database(self):
        os.makedirs(self.storage_dir, exist_ok=True)

        with self.get_db_connection() as conn:
            cursor = conn.cursor()

            cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS class_data (
                    class_key TEXT PRIMARY KEY,
                    grade TEXT NOT NULL,
                    class_no TEXT NOT NULL,
                    pair_mode TEXT NOT NULL,
                    students_json TEXT NOT NULL,
                    seat_map_json TEXT NOT NULL
                )
                """
            )

            cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS app_state (
                    state_key TEXT PRIMARY KEY,
                    value_json TEXT NOT NULL
                )
                """
            )

            cursor.execute("PRAGMA table_info(class_data)")
            existing_columns = {row[1] for row in cursor.fetchall()}

            if "layout_cols" not in existing_columns:
                cursor.execute(
                    """
                    ALTER TABLE class_data
                    ADD COLUMN layout_cols INTEGER NOT NULL DEFAULT 6
                    """
                )

            conn.commit()

    def serialize_value(self, value):
        return json.dumps(value, ensure_ascii=False)

    def deserialize_value(self, raw_value, default):
        if raw_value is None:
            return default

        try:
            return json.loads(raw_value)
        except Exception:
            return default

    def is_database_empty(self):
        with self.get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM class_data")
            class_count = cursor.fetchone()[0]
            cursor.execute("SELECT COUNT(*) FROM app_state")
            state_count = cursor.fetchone()[0]

        return class_count == 0 and state_count == 0

    def find_legacy_json(self, filenames):
        candidate_dirs = [self.runtime_dir]

        current_dir = os.getcwd()
        if current_dir not in candidate_dirs:
            candidate_dirs.append(current_dir)

        for directory in candidate_dirs:
            for filename in filenames:
                path = os.path.join(directory, filename)
                loaded = self.load_json_file(path)
                if loaded:
                    return loaded

        return {}

    def save_all_data_from_dict(self, data):
        with self.get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("DELETE FROM class_data")

            for class_key, value in data.items():
                grade = str(value.get("grade", ""))
                class_no = str(value.get("class", ""))
                layout_cols = self.normalize_layout_cols(
                    value.get("layout_cols", self.DEFAULT_LAYOUT_COLS)
                )
                pair_mode = self.get_effective_pair_mode(
                    layout_cols,
                    value.get("pair_mode", "짝 있음")
                )
                students = value.get("students", [])
                seat_map = value.get("seat_map", {})

                cursor.execute(
                    """
                    INSERT OR REPLACE INTO class_data
                    (class_key, grade, class_no, layout_cols, pair_mode, students_json, seat_map_json)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        class_key,
                        grade,
                        class_no,
                        layout_cols,
                        pair_mode,
                        self.serialize_value(students),
                        self.serialize_value(seat_map),
                    )
                )

            conn.commit()

    def save_app_state_from_dict(self, app_state):
        with self.get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("DELETE FROM app_state")

            for state_key, value in app_state.items():
                cursor.execute(
                    """
                    INSERT OR REPLACE INTO app_state (state_key, value_json)
                    VALUES (?, ?)
                    """,
                    (state_key, self.serialize_value(value))
                )

            conn.commit()

    def migrate_json_to_db_if_needed(self):
        if not self.is_database_empty():
            return

        legacy_data = self.find_legacy_json(self.LEGACY_DATA_FILES)
        legacy_app_state = self.find_legacy_json(self.LEGACY_STATE_FILES)

        if legacy_data:
            upgraded_data = {}

            for class_key, value in legacy_data.items():
                upgraded, _ = self.upgrade_loaded_class_data(value)
                if upgraded:
                    upgraded_data[class_key] = upgraded

            self.save_all_data_from_dict(upgraded_data)

        if legacy_app_state:
            self.save_app_state_from_dict(legacy_app_state)

    def load_all_data(self):
        loaded_data = {}

        with self.get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """
                SELECT class_key, grade, class_no, layout_cols, pair_mode, students_json, seat_map_json
                FROM class_data
                """
            )

            for class_key, grade, class_no, layout_cols, pair_mode, students_json, seat_map_json in cursor.fetchall():
                loaded_data[class_key] = {
                    "grade": grade,
                    "class": class_no,
                    "layout_cols": self.normalize_layout_cols(layout_cols),
                    "pair_mode": self.get_effective_pair_mode(layout_cols, pair_mode),
                    "students": self.deserialize_value(students_json, []),
                    "seat_map": self.deserialize_value(seat_map_json, {}),
                }

        return loaded_data

    def save_all_data(self):
        self.save_all_data_from_dict(self.data)

    def load_app_state(self):
        loaded_state = {}

        with self.get_db_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT state_key, value_json FROM app_state")

            for state_key, value_json in cursor.fetchall():
                loaded_state[state_key] = self.deserialize_value(value_json, "")

        return loaded_state

    def save_app_state(self):
        self.save_app_state_from_dict(self.app_state)

    def remember_current_class_as_last_opened(self):
        if self.current_grade and self.current_class:
            self.app_state["last_opened_class_key"] = self.class_key(
                self.current_grade, self.current_class
            )
            self.save_app_state()

    def load_class_data(self, grade, class_no):
        key = self.class_key(grade, class_no)
        loaded = self.data.get(key)

        upgraded, changed = self.upgrade_loaded_class_data(loaded)
        if not upgraded:
            return None

        if changed:
            self.data[key] = upgraded
            self.save_all_data()

        return upgraded

    def restore_last_opened_class(self):
        last_key = self.app_state.get("last_opened_class_key", "")
        if not last_key or "-" not in last_key:
            return

        grade, class_no = last_key.split("-", 1)
        loaded = self.load_class_data(grade, class_no)
        if not loaded:
            return

        self.current_grade = str(loaded.get("grade", ""))
        self.current_class = str(loaded.get("class", ""))
        self.current_layout_cols = self.normalize_layout_cols(
            loaded.get("layout_cols", self.DEFAULT_LAYOUT_COLS)
        )
        self.pair_mode = self.get_effective_pair_mode(
            self.current_layout_cols,
            loaded.get("pair_mode", "짝 있음")
        )
        self.students = loaded.get("students", [])
        self.seat_map = self.normalize_loaded_seat_map(
            loaded.get("seat_map", {}),
            self.students,
            self.current_layout_cols
        )
        self.selected_seat = None
        self.update_class_info_label()

        self.auto_save_without_message()

    def auto_save_without_message(self):
        if not self.current_grade or not self.current_class:
            return

        key = self.class_key(self.current_grade, self.current_class)
        self.data[key] = {
            "grade": self.current_grade,
            "class": self.current_class,
            "layout_cols": self.current_layout_cols,
            "pair_mode": self.get_effective_pair_mode(self.current_layout_cols, self.pair_mode),
            "students": self.students,
            "seat_map": self.seat_map
        }
        self.save_all_data()
        self.remember_current_class_as_last_opened()

    def save_current_class_data(self):
        if not self.current_grade or not self.current_class:
            messagebox.showwarning("안내", "먼저 설정에서 학년과 반을 입력해 주세요.")
            return

        self.auto_save_without_message()
        messagebox.showinfo(
            "저장",
            f"{self.current_grade}학년 {self.current_class}반 정보가 저장되었습니다."
        )

    # ----------------------------
    # 좌석 생성 규칙
    # ----------------------------
    def get_active_positions_by_student_count(self, count: int, layout_cols=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )

        all_positions = [(r, c) for r in range(self.MAX_ROWS) for c in range(cols)]
        max_seats = self.get_max_seats(cols)
        remove_count = max(max_seats - count, 0)

        removal_order = []
        for r in range(self.MAX_ROWS - 1, -1, -1):
            for c in range(cols - 1, -1, -1):
                removal_order.append((r, c))

        removed_positions = set(removal_order[:remove_count])
        active_positions = [pos for pos in all_positions if pos not in removed_positions]
        return active_positions

    def normalize_loaded_seat_map(self, loaded_map, students, layout_cols=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )

        active_positions = self.get_active_positions_by_student_count(len(students), cols)
        active_keys = [self.pos_key(pos) for pos in active_positions]
        active_key_set = set(active_keys)

        normalized = {}
        used_students = set()

        for key in active_keys:
            value = loaded_map.get(key)
            if not value:
                continue

            student = value.get("student", "")
            if student and student in students and student not in used_students:
                normalized[key] = {
                    "student": student,
                    "locked": bool(value.get("locked", False))
                }
                used_students.add(student)

        ordered_existing_keys = self.get_ordered_position_keys(cols)
        for key in ordered_existing_keys:
            if key in normalized or key not in active_key_set:
                continue

            value = loaded_map.get(key)
            if not value:
                continue

            student = value.get("student", "")
            if student and student in students and student not in used_students:
                normalized[key] = {
                    "student": student,
                    "locked": bool(value.get("locked", False))
                }
                used_students.add(student)

        remaining_students = [s for s in students if s not in used_students]
        missing_keys = [k for k in active_keys if k not in normalized]

        for i, key in enumerate(missing_keys):
            normalized[key] = {
                "student": remaining_students[i] if i < len(remaining_students) else "",
                "locked": False
            }

        return normalized

    def rebuild_seat_map_preserving_valid_positions(self, old_map, students, layout_cols=None):
        cols = self.normalize_layout_cols(
            self.current_layout_cols if layout_cols is None else layout_cols
        )

        active_positions = self.get_active_positions_by_student_count(len(students), cols)
        active_keys = [self.pos_key(pos) for pos in active_positions]
        active_key_set = set(active_keys)

        ordered_old_keys = self.get_ordered_position_keys(6)
        ordered_old_keys.extend(
            key for key in old_map.keys()
            if key not in ordered_old_keys
        )

        ordered_students = []
        used_students = set()

        for key in ordered_old_keys:
            value = old_map.get(key)
            if not value:
                continue

            student = value.get("student", "")
            if student in students and student not in used_students:
                if key in active_key_set:
                    ordered_students.append(student)
                    used_students.add(student)

        for key in ordered_old_keys:
            value = old_map.get(key)
            if not value:
                continue

            student = value.get("student", "")
            if student in students and student not in used_students:
                ordered_students.append(student)
                used_students.add(student)

        for student in students:
            if student not in used_students:
                ordered_students.append(student)
                used_students.add(student)

        seat_map = {}
        for i, key in enumerate(active_keys):
            old_value = old_map.get(key, {})
            seat_map[key] = {
                "student": ordered_students[i] if i < len(ordered_students) else "",
                "locked": bool(old_value.get("locked", False)) if key in active_key_set else False
            }

        return seat_map

    # ----------------------------
    # 메인 UI
    # ----------------------------
    def build_ui(self):
        top_frame = tk.Frame(self.root, bg="#dff3ff")
        top_frame.pack(fill="x", pady=10, padx=12)

        self.title_label = tk.Label(
            top_frame,
            text="클래스픽",
            font=("맑은 고딕", 18, "bold"),
            bg="#dff3ff"
        )
        self.title_label.pack(side="left")

        self.class_info_label = tk.Label(
            top_frame,
            text="학년/반 미설정",
            font=("맑은 고딕", 11, "bold"),
            bg="#dff3ff",
            fg="#1f4e79"
        )
        self.class_info_label.pack(side="left", padx=16)

        button_frame = tk.Frame(top_frame, bg="#dff3ff")
        button_frame.pack(side="right")

        tk.Button(button_frame, text="설정", width=10, command=self.open_settings_window).pack(side="left", padx=4)
        tk.Button(button_frame, text="저장", width=10, command=self.save_current_class_data).pack(side="left", padx=4)
        tk.Button(button_frame, text="내보내기", width=10, command=self.export_to_png).pack(side="left", padx=4)

        desk_frame = tk.Frame(self.root, bg="#dff3ff")
        desk_frame.pack(pady=10)

        tk.Label(
            desk_frame,
            text="교     탁",
            font=("맑은 고딕", 18, "bold"),
            width=12,
            height=2,
            relief="solid",
            bd=2,
            bg="#ffffff"
        ).pack()

        self.canvas = tk.Canvas(
            self.root,
            bg="#eef9ff",
            highlightthickness=0
        )
        self.canvas.pack(fill="both", expand=True, padx=20, pady=10)

        bottom_frame = tk.Frame(self.root, bg="#dff3ff")
        bottom_frame.pack(pady=12)

        self.shuffle_button = tk.Button(
            bottom_frame,
            text="자리배치",
            font=("맑은 고딕", 14, "bold"),
            width=14,
            height=2,
            command=self.start_shuffle_animation
        )
        self.shuffle_button.pack()

    # ----------------------------
    # 설정 창
    # ----------------------------
    def open_settings_window(self):
        win = tk.Toplevel(self.root)
        win.title("설정")
        win.resizable(False, False)

        desired_width = 760
        desired_height = 780

        left, top, right, bottom = self.get_work_area()
        area_width = right - left
        area_height = bottom - top

        width = min(desired_width, area_width - 40)
        height = min(desired_height, area_height - 40)

        width = max(width, 680)
        height = max(height, 720)

        self.center_window_in_work_area(win, width, height)

        main_frame = tk.Frame(win)
        main_frame.pack(fill="both", expand=True, padx=20, pady=20)

        vcmd = (win.register(self.validate_numeric_input), "%P")

        grade_class_frame = tk.Frame(main_frame)
        grade_class_frame.pack(fill="x")

        grade_frame = tk.Frame(grade_class_frame)
        grade_frame.pack(side="left", fill="x", expand=True, padx=(0, 10))

        class_frame = tk.Frame(grade_class_frame)
        class_frame.pack(side="left", fill="x", expand=True)

        tk.Label(grade_frame, text="학년", font=("맑은 고딕", 11, "bold")).pack(anchor="w", pady=(0, 4))
        grade_entry = tk.Entry(
            grade_frame,
            font=("맑은 고딕", 11),
            width=12,
            validate="key",
            validatecommand=vcmd
        )
        grade_entry.pack(fill="x")
        grade_entry.insert(0, self.current_grade)

        tk.Label(class_frame, text="반", font=("맑은 고딕", 11, "bold")).pack(anchor="w", pady=(0, 4))
        class_entry = tk.Entry(
            class_frame,
            font=("맑은 고딕", 11),
            width=12,
            validate="key",
            validatecommand=vcmd
        )
        class_entry.pack(fill="x")
        class_entry.insert(0, self.current_class)

        tk.Label(main_frame, text="학생 이름 입력", font=("맑은 고딕", 11, "bold")).pack(anchor="w", pady=(24, 4))
        self.student_hint_label = tk.Label(
            main_frame,
            text="예: 01. 김철수\n한 줄에 한 명씩 입력하면 자동으로 번호가 정리됩니다.",
            font=("맑은 고딕", 9),
            fg="gray",
            justify="left",
            anchor="w"
        )
        self.student_hint_label.pack(anchor="w", fill="x", pady=(0, 6))

        text_frame = tk.Frame(main_frame)
        text_frame.pack(fill="both", expand=True, pady=10)

        text_scrollbar = tk.Scrollbar(text_frame, orient="vertical")
        text_box = tk.Text(
            text_frame,
            width=60,
            height=20,
            font=("맑은 고딕", 10),
            yscrollcommand=text_scrollbar.set
        )
        text_scrollbar.config(command=text_box.yview)

        text_box.pack(side="left", fill="both", expand=True)
        text_scrollbar.pack(side="right", fill="y")

        if self.students:
            text_box.insert("1.0", "\n".join(self.students))

        option_row = tk.Frame(main_frame)
        option_row.pack(fill="x", pady=(10, 4))

        pair_box = tk.Frame(option_row)
        pair_box.pack(side="left", fill="x", expand=True)

        layout_box = tk.Frame(option_row)
        layout_box.pack(side="left", fill="x", expand=True, padx=(24, 0))

        pair_label = tk.Label(pair_box, text="짝 설정", font=("맑은 고딕", 11, "bold"))
        pair_label.pack(anchor="w", pady=(0, 4))

        pair_var = tk.StringVar(value=self.get_effective_pair_mode(self.current_layout_cols, self.pair_mode))
        pair_frame = tk.Frame(pair_box)
        pair_frame.pack(anchor="w", pady=(0, 4))

        pair_yes_radio = tk.Radiobutton(
            pair_frame,
            text="짝 있음",
            variable=pair_var,
            value="짝 있음",
            font=("맑은 고딕", 10)
        )
        pair_yes_radio.pack(side="left", padx=(0, 16))

        pair_no_radio = tk.Radiobutton(
            pair_frame,
            text="짝 없음",
            variable=pair_var,
            value="짝 없음",
            font=("맑은 고딕", 10)
        )
        pair_no_radio.pack(side="left")

        layout_label = tk.Label(layout_box, text="배열 설정", font=("맑은 고딕", 11, "bold"))
        layout_label.pack(anchor="w", pady=(0, 4))

        layout_cols_var = tk.IntVar(value=self.current_layout_cols)
        layout_frame = tk.Frame(layout_box)
        layout_frame.pack(anchor="w", pady=(0, 4))

        layout_five_radio = tk.Radiobutton(
            layout_frame,
            text="5열",
            variable=layout_cols_var,
            value=5,
            font=("맑은 고딕", 10)
        )
        layout_five_radio.pack(side="left", padx=(0, 16))

        layout_six_radio = tk.Radiobutton(
            layout_frame,
            text="6열",
            variable=layout_cols_var,
            value=6,
            font=("맑은 고딕", 10)
        )
        layout_six_radio.pack(side="left")

        max_students_label = tk.Label(
            main_frame,
            text="",
            font=("맑은 고딕", 9),
            fg="#4a6b82",
            anchor="w",
            justify="left"
        )
        max_students_label.pack(anchor="w", fill="x", pady=(6, 0))

        def update_pair_controls():
            cols = self.normalize_layout_cols(layout_cols_var.get())
            is_six_columns = cols == 6

            pair_state = "normal" if is_six_columns else "disabled"
            pair_yes_radio.config(state=pair_state)
            pair_no_radio.config(state=pair_state)
            pair_label.config(fg="#000000" if is_six_columns else "gray")

            if not is_six_columns:
                pair_var.set("짝 없음")

            max_students_label.config(
                text=f"현재 선택한 배열의 최대 인원: {self.get_max_seats(cols)}명"
            )

        layout_cols_var.trace_add("write", lambda *args: update_pair_controls())
        update_pair_controls()

        def on_load():
            grade = grade_entry.get().strip()
            class_no = class_entry.get().strip()

            if not grade or not class_no:
                messagebox.showwarning("안내", "학년과 반을 입력해 주세요.")
                return

            if not grade.isdigit() or not class_no.isdigit():
                messagebox.showwarning("안내", "학년과 반에는 숫자만 입력할 수 있습니다.")
                return

            loaded = self.load_class_data(grade, class_no)
            if not loaded:
                messagebox.showinfo("불러오기", "저장된 데이터가 없습니다. 새로 설정하시면 됩니다.")
                return

            text_box.delete("1.0", "end")
            text_box.insert("1.0", "\n".join(loaded.get("students", [])))

            loaded_cols = self.normalize_layout_cols(
                loaded.get("layout_cols", self.DEFAULT_LAYOUT_COLS)
            )
            layout_cols_var.set(loaded_cols)
            pair_var.set(
                self.get_effective_pair_mode(loaded_cols, loaded.get("pair_mode", "짝 있음"))
            )
            update_pair_controls()

            messagebox.showinfo("불러오기", f"{grade}학년 {class_no}반 데이터를 불러왔습니다.")

        def on_apply():
            grade = grade_entry.get().strip()
            class_no = class_entry.get().strip()
            raw_students_text = text_box.get("1.0", "end")
            layout_cols = self.normalize_layout_cols(layout_cols_var.get())
            pair_mode = self.get_effective_pair_mode(layout_cols, pair_var.get())

            if not grade or not class_no:
                messagebox.showwarning("안내", "학년과 반을 입력해 주세요.")
                return

            if not grade.isdigit() or not class_no.isdigit():
                messagebox.showwarning("안내", "학년과 반에는 숫자만 입력할 수 있습니다.")
                return

            is_valid, error_message = self.validate_student_input(raw_students_text)
            if not is_valid:
                messagebox.showwarning("안내", error_message)
                return

            students = self.parse_students_text(raw_students_text)
            max_seats = self.get_max_seats(layout_cols)

            if len(students) > max_seats:
                messagebox.showwarning("안내", f"{layout_cols}열 배열은 최대 {max_seats}명까지 가능합니다.")
                return

            loaded = self.load_class_data(grade, class_no)

            self.current_grade = grade
            self.current_class = class_no
            self.current_layout_cols = layout_cols
            self.pair_mode = pair_mode
            self.students = students
            self.selected_seat = None

            if (
                loaded
                and loaded.get("students") == students
                and self.normalize_layout_cols(
                    loaded.get("layout_cols", self.DEFAULT_LAYOUT_COLS)
                ) == layout_cols
            ):
                self.seat_map = self.normalize_loaded_seat_map(
                    loaded.get("seat_map", {}),
                    students,
                    layout_cols
                )
            else:
                self.seat_map = self.rebuild_seat_map_preserving_valid_positions(
                    self.seat_map,
                    students,
                    layout_cols
                )

            self.update_class_info_label()
            self.redraw_seats()
            self.auto_save_without_message()
            win.destroy()

        btn_frame = tk.Frame(main_frame)
        btn_frame.pack(pady=(18, 0))

        tk.Button(btn_frame, text="불러오기", width=12, command=on_load).pack(side="left", padx=6)
        tk.Button(btn_frame, text="적용", width=12, command=on_apply).pack(side="left", padx=6)
        tk.Button(btn_frame, text="취소", width=12, command=win.destroy).pack(side="left", padx=6)

    # ----------------------------
    # 좌석 화면 갱신
    # ----------------------------
    def update_class_info_label(self):
        if self.current_grade and self.current_class:
            self.class_info_label.config(
                text=f"{self.current_grade}학년 {self.current_class}반 · {self.current_layout_cols}열"
            )
        else:
            self.class_info_label.config(text="학년/반 미설정")

    def redraw_seats(self):
        self.canvas.delete("all")
        self.seat_widgets.clear()
        self.resize_after_id = None

        canvas_width = max(self.canvas.winfo_width(), 860)
        canvas_height = max(self.canvas.winfo_height(), 420)

        if not self.students:
            self.canvas.create_text(
                canvas_width / 2,
                canvas_height / 2,
                text="설정 버튼을 눌러 학년, 반, 학생 명단을 입력해 주세요.",
                font=("맑은 고딕", 14, "bold"),
                fill="#3b5f7a"
            )
            self.canvas.config(scrollregion=(0, 0, canvas_width, canvas_height))
            return

        active_positions = self.get_active_positions_by_student_count(
            len(self.students),
            self.current_layout_cols
        )
        coords, total_width, total_height = self.calculate_seat_positions(active_positions)

        canvas_width = max(self.canvas.winfo_width(), total_width + 48, 860)
        canvas_height = max(self.canvas.winfo_height(), total_height + 48, 420)
        self.canvas.config(scrollregion=(0, 0, canvas_width, canvas_height))

        for pos in active_positions:
            key = self.pos_key(pos)
            x, y = coords[pos]
            seat_data = self.seat_map.get(key, {"student": "", "locked": False})
            self.draw_single_seat(key, x, y, seat_data)

    def calculate_seat_positions(self, active_positions):
        coords = {}
        cols = self.current_layout_cols
        pair_mode = self.get_effective_pair_mode()

        canvas_width = max(self.canvas.winfo_width(), 860)
        canvas_height = max(self.canvas.winfo_height(), 420)

        total_width = self.get_total_layout_width(
            cols,
            self.SEAT_WIDTH,
            pair_mode,
            self.PAIR_INNER_GAP,
            self.PAIR_OUTER_GAP,
            self.NORMAL_GAP,
        )
        total_height = self.MAX_ROWS * self.SEAT_HEIGHT + (self.MAX_ROWS - 1) * self.ROW_GAP

        start_x = max((canvas_width - total_width) // 2, 24)
        start_y = max((canvas_height - total_height) // 2, 24)

        x_positions = self.build_column_positions(
            cols,
            start_x,
            self.SEAT_WIDTH,
            pair_mode,
            self.PAIR_INNER_GAP,
            self.PAIR_OUTER_GAP,
            self.NORMAL_GAP,
        )

        active_set = set(active_positions)

        for r in range(self.MAX_ROWS):
            y = start_y + r * (self.SEAT_HEIGHT + self.ROW_GAP)

            for c in range(cols):
                pos = (r, c)
                if pos in active_set:
                    coords[pos] = (x_positions[c], y)

        return coords, total_width, total_height

    def draw_single_seat(self, key, x, y, seat_data):
        student = seat_data.get("student", "")
        locked = seat_data.get("locked", False)
        is_selected = (self.selected_seat == key)

        fill_color = "#dff8d6" if locked else "#f9fff0"
        outline_color = "#d62828" if is_selected else "#4d4d4d"
        outline_width = 4 if is_selected else 1

        rect_id = self.canvas.create_rectangle(
            x, y, x + self.SEAT_WIDTH, y + self.SEAT_HEIGHT,
            fill=fill_color,
            outline=outline_color,
            width=outline_width
        )

        text_id = self.canvas.create_text(
            x + self.SEAT_WIDTH / 2,
            y + self.SEAT_HEIGHT / 2 - 2,
            text=student,
            font=("맑은 고딕", 12, "bold"),
            fill="#202020",
            width=self.SEAT_WIDTH - 12
        )

        lock_text = "🔒" if locked else "🔓"
        lock_id = self.canvas.create_text(
            x + self.SEAT_WIDTH - 12,
            y + self.SEAT_HEIGHT - 10,
            text=lock_text,
            font=("맑은 고딕", 12),
            fill="#1f4e79"
        )

        self.seat_widgets[key] = {
            "rect": rect_id,
            "text": text_id,
            "lock": lock_id,
            "x": x,
            "y": y
        }

        self.canvas.tag_bind(rect_id, "<Button-1>", lambda e, k=key: self.on_seat_click(k))
        self.canvas.tag_bind(text_id, "<Button-1>", lambda e, k=key: self.on_seat_click(k))
        self.canvas.tag_bind(lock_id, "<Button-1>", lambda e, k=key: self.on_lock_click(k))

    # ----------------------------
    # 자리 클릭 / 고정
    # ----------------------------
    def on_lock_click(self, key):
        if self.animating:
            return

        seat = self.seat_map.get(key)
        if not seat:
            return

        seat["locked"] = not seat["locked"]

        if self.selected_seat == key:
            self.selected_seat = None

        self.auto_save_without_message()
        self.redraw_seats()

    def on_seat_click(self, key):
        if self.animating:
            return

        seat = self.seat_map.get(key)
        if not seat:
            return

        if seat.get("locked", False):
            return

        if self.selected_seat is None:
            self.selected_seat = key
            self.redraw_seats()
            return

        if self.selected_seat == key:
            self.selected_seat = None
            self.redraw_seats()
            return

        first = self.seat_map.get(self.selected_seat)
        second = self.seat_map.get(key)

        if not first or not second:
            self.selected_seat = None
            self.redraw_seats()
            return

        if first.get("locked", False) or second.get("locked", False):
            self.selected_seat = None
            self.redraw_seats()
            return

        first["student"], second["student"] = second["student"], first["student"]
        self.selected_seat = None

        self.auto_save_without_message()
        self.redraw_seats()

    # ----------------------------
    # 랜덤 자리배치
    # ----------------------------
    def start_shuffle_animation(self):
        if self.animating:
            return

        if not self.students:
            messagebox.showwarning("안내", "먼저 설정을 완료해 주세요.")
            return

        unlocked_keys = []
        unlocked_students = []

        for key, value in self.seat_map.items():
            if not value.get("locked", False):
                unlocked_keys.append(key)
                unlocked_students.append(value.get("student", ""))

        if len(unlocked_keys) <= 1:
            messagebox.showinfo("안내", "랜덤 배치할 수 있는 고정되지 않은 자리가 부족합니다.")
            return

        self.selected_seat = None
        self.final_shuffle_result = unlocked_students[:]
        random.shuffle(self.final_shuffle_result)

        self.animating = True
        self.shuffle_button.config(state="disabled")
        self.run_shuffle_animation(unlocked_keys, 0, 12)

    def run_shuffle_animation(self, unlocked_keys, step, max_steps):
        temp_students = [self.seat_map[k]["student"] for k in unlocked_keys]
        random.shuffle(temp_students)

        for i, key in enumerate(unlocked_keys):
            self.seat_map[key]["student"] = temp_students[i]

        self.redraw_seats()

        if step < max_steps:
            self.animation_job = self.root.after(
                90,
                lambda: self.run_shuffle_animation(unlocked_keys, step + 1, max_steps)
            )
        else:
            for i, key in enumerate(unlocked_keys):
                self.seat_map[key]["student"] = self.final_shuffle_result[i]

            self.animating = False
            self.final_shuffle_result = None
            self.shuffle_button.config(state="normal")

            self.auto_save_without_message()
            self.redraw_seats()

    # ----------------------------
    # 내보내기 레이아웃
    # ----------------------------
    def get_export_layout(self, seat_count: int):
        width = 980
        height = 700

        cols = self.current_layout_cols
        pair_mode = self.get_effective_pair_mode()
        active_positions = self.get_active_positions_by_student_count(seat_count, cols)

        seat_width = 128
        seat_height = 72
        row_gap = 22
        pair_inner_gap = 8
        pair_outer_gap = 36
        normal_gap = 22

        total_width = self.get_total_layout_width(
            cols,
            seat_width,
            pair_mode,
            pair_inner_gap,
            pair_outer_gap,
            normal_gap,
        )
        start_x = (width - total_width) // 2
        start_y = 60

        x_positions = self.build_column_positions(
            cols,
            start_x,
            seat_width,
            pair_mode,
            pair_inner_gap,
            pair_outer_gap,
            normal_gap,
        )

        coords = {}

        for r in range(self.MAX_ROWS):
            y = start_y + r * (seat_height + row_gap)

            for c in range(cols):
                rotated_r = self.MAX_ROWS - 1 - r
                rotated_c = cols - 1 - c
                rotated_pos = (rotated_r, rotated_c)

                if rotated_pos in active_positions:
                    coords[rotated_pos] = (x_positions[c], y)

        desk_width = 280
        desk_height = 76
        desk_x1 = (width - desk_width) // 2
        desk_y1 = 545
        desk_x2 = desk_x1 + desk_width
        desk_y2 = desk_y1 + desk_height

        bottom_row_y = start_y + (self.MAX_ROWS - 1) * (seat_height + row_gap)
        gap_top = bottom_row_y + seat_height
        gap_bottom = desk_y1
        side_label_y = int((gap_top + gap_bottom) / 2) - 12

        return {
            "width": width,
            "height": height,
            "desk": (desk_x1, desk_y1, desk_x2, desk_y2),
            "seat_width": seat_width,
            "seat_height": seat_height,
            "coords": coords,
            "active_positions": active_positions,
            "side_label_y": side_label_y,
        }

    # ----------------------------
    # PNG 내보내기
    # ----------------------------
    def export_to_png(self):
        if not self.current_grade or not self.current_class:
            messagebox.showwarning("안내", "먼저 학년과 반을 설정해 주세요.")
            return

        if not self.students:
            messagebox.showwarning("안내", "학생 명단이 없습니다.")
            return

        if not PIL_AVAILABLE:
            messagebox.showwarning("안내", "PNG 저장을 위해 Pillow가 필요합니다.\npip install pillow")
            return

        self.auto_save_without_message()

        layout = self.get_export_layout(len(self.students))
        width = layout["width"]
        height = layout["height"]

        img = Image.new("RGB", (width, height), "#ffffff")
        draw = ImageDraw.Draw(img)

        font_desk = self.get_font(28, bold=True)
        font_name = self.get_font(19, bold=True)
        font_side = self.get_font(22, bold=True)

        desk_x1, desk_y1, desk_x2, desk_y2 = layout["desk"]
        seat_width = layout["seat_width"]
        seat_height = layout["seat_height"]
        coords = layout["coords"]
        active_positions = layout["active_positions"]
        side_label_y = layout["side_label_y"]

        for pos in active_positions:
            key = self.pos_key(pos)
            x, y = coords[pos]

            seat = self.seat_map.get(key, {"student": "", "locked": False})
            name = seat.get("student", "")

            draw.rectangle(
                (x, y, x + seat_width, y + seat_height),
                outline="#7a7a7a",
                width=2,
                fill="#ffffff"
            )

            self.draw_centered_text(
                draw,
                x,
                y,
                seat_width,
                seat_height,
                name,
                font_name,
                "#222222"
            )

        draw.rectangle(
            (desk_x1, desk_y1, desk_x2, desk_y2),
            outline="#222222",
            width=3,
            fill="#ffffff"
        )
        self.draw_centered_text(
            draw,
            desk_x1,
            desk_y1,
            desk_x2 - desk_x1,
            desk_y2 - desk_y1,
            "교     탁",
            font_desk,
            "#111111"
        )

        hall_text = "복도"
        window_text = "창문"

        hall_x = 85
        hall_y = side_label_y

        window_bbox = draw.textbbox((0, 0), window_text, font=font_side)
        window_w = window_bbox[2] - window_bbox[0]
        window_x = width - 85 - window_w
        window_y = side_label_y

        draw.text((hall_x, hall_y), hall_text, font=font_side, fill="#444444")
        draw.text((window_x, window_y), window_text, font=font_side, fill="#444444")

        filename = (
            datetime.now().strftime("%y%m%d")
            + f"_{self.current_grade}학년{self.current_class}반_{self.current_layout_cols}열_자리표.png"
        )
        desktop = self.get_desktop_path()
        save_path = os.path.join(desktop, filename)

        try:
            img.save(save_path)
            messagebox.showinfo("내보내기", f"PNG 파일이 저장되었습니다.\n{save_path}")
        except Exception as e:
            messagebox.showerror("내보내기 실패", f"파일 저장 중 오류가 발생했습니다.\n{e}")

    def get_font(self, size, bold=False):
        candidate_paths = [
            "C:/Windows/Fonts/malgunbd.ttf" if bold else "C:/Windows/Fonts/malgun.ttf",
            "/System/Library/Fonts/AppleSDGothicNeo.ttc",
            "/System/Library/Fonts/Supplemental/AppleGothic.ttf",
        ]

        for path in candidate_paths:
            if os.path.exists(path):
                try:
                    return ImageFont.truetype(path, size)
                except Exception:
                    pass

        return ImageFont.load_default()

    def draw_centered_text(self, draw, x, y, w, h, text, font, fill):
        bbox = draw.multiline_textbbox((0, 0), text, font=font, align="center")
        text_w = bbox[2] - bbox[0]
        text_h = bbox[3] - bbox[1]
        tx = x + (w - text_w) / 2
        ty = y + (h - text_h) / 2 - 2
        draw.multiline_text((tx, ty), text, font=font, fill=fill, align="center")


if __name__ == "__main__":
    root = tk.Tk()
    app = SeatingProgram(root)
    root.mainloop()
