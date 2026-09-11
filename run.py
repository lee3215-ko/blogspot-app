"""블로그스팟 글 작성 프로그램 실행 진입점."""
from paths import APP_NAME, APP_VERSION, get_icon_path, get_update_version_url, init_runtime_paths

init_runtime_paths()


def _preload_frozen_deps():
    import selenium.webdriver.chrome.options  # noqa: F401
    import selenium.webdriver.chrome.service  # noqa: F401
    import selenium.webdriver.chrome.webdriver  # noqa: F401
    import selenium.webdriver.remote.webdriver  # noqa: F401
    import webdriver_manager.chrome  # noqa: F401


_preload_frozen_deps()

from app import BloggerApp

try:
    import customtkinter as ctk
except ImportError:
    ctk = None


if __name__ == "__main__":
    root = ctk.CTk() if ctk else __import__("tkinter").Tk()
    icon = get_icon_path()
    if icon:
        try:
            root.iconbitmap(default=icon)
        except Exception:
            pass
    root.title(f"블로그스팟 글 작성  {APP_VERSION}")
    app = BloggerApp(root)
    from update_ui import schedule_update_check

    schedule_update_check(
        root,
        version_url=get_update_version_url(),
        current_version=APP_VERSION,
        app_name=APP_NAME,
        exe_name="BloggerSpot.exe",
        zip_inner_folder="BloggerSpot",
        log_callback=app.log,
    )
    root.mainloop()
