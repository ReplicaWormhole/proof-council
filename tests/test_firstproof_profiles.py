from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = REPO_ROOT / "scripts" / "firstproof_entrypoint.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("_firstproof_entrypoint_profiles_test", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


fp = _load_module()


def _clear_firstproof_env(monkeypatch):
    for key in list(fp.os.environ):
        if key.startswith("FIRSTPROOF_"):
            monkeypatch.delenv(key, raising=False)
def test_firstproof_defaults_to_submission_workflow(monkeypatch):
    _clear_firstproof_env(monkeypatch)

    settings = fp._settings()

    assert settings.workflow == "firstproof_submission"
    assert settings.n_rounds == 10
    assert settings.round_batch_size == 5
    assert settings.adaptive_continuation is True
    assert settings.adaptive_max_rounds == 200
    assert settings.budget_usd_per_question == 1000.0


def test_firstproof_submission_profile_restores_adaptive_continuation(monkeypatch):
    _clear_firstproof_env(monkeypatch)
    monkeypatch.setenv("FIRSTPROOF_PROFILE", "firstproof_submission")

    settings = fp._settings()

    assert settings.workflow == "firstproof_submission"
    assert settings.n_rounds == 10
    assert settings.round_batch_size == 5
    assert settings.adaptive_continuation is True
    assert settings.adaptive_max_rounds == 200
    assert settings.budget_usd_per_question == 1000.0
    assert fp._round_schedule(settings)[:3] == [5, 10, 15]
    assert fp._round_schedule(settings)[-1] == 200


def test_firstproof_env_overrides_profile_defaults(monkeypatch):
    _clear_firstproof_env(monkeypatch)
    monkeypatch.setenv("FIRSTPROOF_PROFILE", "firstproof_submission")
    monkeypatch.setenv("FIRSTPROOF_N_ROUNDS", "12")
    monkeypatch.setenv("FIRSTPROOF_BUDGET_USD_PER_QUESTION", "123")

    settings = fp._settings()

    assert settings.n_rounds == 12
    assert settings.budget_usd_per_question == 123.0
    assert fp._round_schedule(settings)[:3] == [5, 10, 15]
    assert fp._round_schedule(settings)[-1] == 200
