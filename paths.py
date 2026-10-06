"""????棺堉?뤃?????뗭몡????癲?????"""
import os
import sys

APP_NAME = "BloggerSpot"
APP_VERSION = "1.2.16"
UPDATE_VERSION_URL = (
    "https://raw.githubusercontent.com/lee3215-ko/blogspot-app/main/version.json"
)


def get_update_version_url() -> str:
    return (os.environ.get("BLOGGERSPOT_UPDATE_URL") or UPDATE_VERSION_URL).strip()


def is_frozen() -> bool:
    return getattr(sys, "frozen", False)


def get_app_dir() -> str:
    if is_frozen():
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


def get_data_dir() -> str:
    data_dir = os.path.join(get_app_dir(), "data")
    os.makedirs(data_dir, exist_ok=True)
    return data_dir


def data_path(filename: str) -> str:
    return os.path.join(get_data_dir(), filename)


def get_resource_path(*parts: str) -> str:
    if is_frozen():
        base = getattr(sys, "_MEIPASS", get_app_dir())
    else:
        base = get_app_dir()
    return os.path.join(base, *parts)


def get_icon_path() -> str | None:
    ico = get_resource_path("assets", "app_icon.ico")
    if os.path.isfile(ico):
        return ico
    return None


def init_runtime_paths():
    os.chdir(get_app_dir())
    get_data_dir()
