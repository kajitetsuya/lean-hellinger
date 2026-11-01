# Copyright 2026 Tetsuya Kaji
# SPDX-License-Identifier: Apache-2.0
"""Adversarial verifier guards; add --kernel for real pinned Lean fixtures.

These tests exercise the verifier's rejection boundary. They do not establish
the mathematical correctness of the article or replace full verification.
"""
from __future__ import annotations

import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location("snapshot_verifier", ROOT / "scripts" / "verify.py")
verifier = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(verifier)
RUN_KERNEL = "--kernel" in sys.argv
if RUN_KERNEL:
    sys.argv.remove("--kernel")


class JsonGuards(unittest.TestCase):
    def test_duplicate_keys_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            verifier.parse_json('{"files": {}, "files": {}}')

    def test_nonstandard_numeric_constants_are_rejected(self):
        for value in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "Invalid JSON"):
                verifier.parse_json('{"x": ' + value + '}')


class SnapshotGuards(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.names = {"lean-toolchain", "lake-manifest.json", "lakefile.toml", "Hellinger.lean",
                      "declarations.json", "scripts/verify.py", "LICENSE"}
        for name in self.names:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("guard fixture\n", encoding="utf-8")
        self.snapshot = {"schema_version": 1, "version": verifier.VERSION,
                         "files": {name: verifier.digest(self.root / name) for name in self.names}}
        self.save()

    def save(self):
        (self.root / "snapshot.json").write_text(json.dumps(self.snapshot) + "\n", encoding="utf-8")

    def test_valid_inventory_and_generated_cache_exclusions(self):
        for name in (".git/config", ".lake/cache.olean", "scripts/__pycache__/cache.pyc",
                     "verification.json"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("generated\n", encoding="utf-8")
        self.assertEqual(verifier.verify_snapshot(self.root), self.snapshot)

    def test_unlisted_distributable_is_rejected(self):
        (self.root / "Extra.lean").write_text("module\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "file inventory differs"):
            verifier.verify_snapshot(self.root)

    def test_missing_file_is_rejected(self):
        (self.root / "LICENSE").unlink()
        with self.assertRaisesRegex(ValueError, "file inventory differs"):
            verifier.verify_snapshot(self.root)

    def test_changed_file_is_rejected(self):
        (self.root / "Hellinger.lean").write_text("changed\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "hash mismatch"):
            verifier.verify_snapshot(self.root)

    def test_changed_manifest_is_rejected_against_original(self):
        original = copy.deepcopy(self.snapshot)
        (self.root / "LICENSE").write_text("changed\n", encoding="utf-8")
        self.snapshot["files"]["LICENSE"] = verifier.digest(self.root / "LICENSE")
        self.save()
        with self.assertRaisesRegex(ValueError, "manifest changed"):
            verifier.verify_snapshot(self.root, original)

    def test_required_inventory_cannot_be_omitted(self):
        del self.snapshot["files"]["scripts/verify.py"]
        self.save()
        with self.assertRaisesRegex(ValueError, "omits required"):
            verifier.verify_snapshot(self.root)

    def test_path_traversal_and_nonportable_paths_are_rejected(self):
        for path in ("../outside", "a/../../outside", "/outside", "C:/outside", "a\\b",
                     "./LICENSE", "a//b", "a/./b", "LICENSE/", ""):
            with self.subTest(path=path), self.assertRaises(ValueError):
                verifier.local(self.root, path)

    def test_manifest_cannot_list_itself_or_cache(self):
        for name in ("snapshot.json", "verification.json", ".lake/file", "a/__pycache__/file"):
            with self.subTest(name=name):
                snapshot = copy.deepcopy(self.snapshot)
                snapshot["files"][name] = "A" * 64
                (self.root / "snapshot.json").write_text(json.dumps(snapshot), encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "Excluded path"):
                    verifier.verify_snapshot(self.root)

    def test_sha_and_schema_types_are_strict(self):
        for key, value, reason in (("schema_version", True, "version"),
                                   ("files", {"LICENSE": "a" * 64}, "SHA256")):
            with self.subTest(key=key):
                snapshot = copy.deepcopy(self.snapshot)
                snapshot[key] = value
                (self.root / "snapshot.json").write_text(json.dumps(snapshot), encoding="utf-8")
                with self.assertRaisesRegex(ValueError, reason):
                    verifier.verify_snapshot(self.root)

    def test_symlink_escape_is_rejected(self):
        target = self.root / "link"
        try:
            target.symlink_to(self.root.parent, target_is_directory=True)
        except OSError:
            self.skipTest("Creating symlinks is unavailable")
        with self.assertRaises(ValueError):
            verifier.distributable_files(self.root)


class DeclarationGuards(unittest.TestCase):
    def valid_map(self):
        return {"schema_version": 1, "article_doi": verifier.ARTICLE_DOI,
                "results": [{"key": f"result-{index}", "paper": "Theorem 1", "title": "Result",
                             "declaration": name, "related_declarations": []}
                            for index, name in enumerate(sorted(verifier.MAIN_DECLARATIONS))]}

    def test_exact_principal_inventory_and_related_exports(self):
        data = self.valid_map()
        data["results"][0]["related_declarations"] = ["Hellinger.additional_export"]
        rows, names = verifier.check_declarations(data)
        self.assertEqual(len(rows), len(verifier.MAIN_DECLARATIONS))
        self.assertEqual(names, verifier.MAIN_DECLARATIONS | {"Hellinger.additional_export"})

    def test_missing_duplicate_and_replaced_principal_exports_are_rejected(self):
        for change in ("missing", "duplicate", "replaced"):
            with self.subTest(change=change):
                data = self.valid_map()
                if change == "missing":
                    data["results"].pop()
                elif change == "duplicate":
                    data["results"][0]["declaration"] = data["results"][1]["declaration"]
                else:
                    data["results"][0]["declaration"] = "Hellinger.weaker_result"
                with self.assertRaises(ValueError):
                    verifier.check_declarations(data)

    def test_lean_command_injection_is_rejected(self):
        data = self.valid_map()
        data["results"][0]["related_declarations"] = ["Hellinger.foo\n#eval 1"]
        with self.assertRaisesRegex(ValueError, "Malformed Lean declaration"):
            verifier.check_declarations(data)

    def test_duplicate_related_exports_are_rejected(self):
        data = self.valid_map()
        data["results"][0]["related_declarations"] = ["Hellinger.foo", "Hellinger.foo"]
        with self.assertRaisesRegex(ValueError, "Duplicate related"):
            verifier.check_declarations(data)


class ImportGraphGuards(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "Hellinger").mkdir()

    def write(self, module, source):
        (self.root / (module.replace(".", "/") + ".lean")).write_text(source, encoding="utf-8")

    def test_topological_order_ignores_nested_comments_and_strings(self):
        self.write("Hellinger", "module\npublic import Hellinger.B\n")
        self.write("Hellinger.B", "module\n/- import Hellinger.Missing /- nested -/ -/\n"
                   "import all Hellinger.A -- trailing comment\n#eval \"import Hellinger.Missing\"\n")
        self.write("Hellinger.A", "module\n")
        self.assertEqual(verifier.local_import_order(self.root, ["Hellinger", "Hellinger.B", "Hellinger.A"]),
                         ["Hellinger.A", "Hellinger.B", "Hellinger"])

    def test_missing_local_import_is_rejected(self):
        self.write("Hellinger", "module\nimport Hellinger.Missing\n")
        with self.assertRaisesRegex(ValueError, "Missing local import"):
            verifier.local_import_order(self.root, ["Hellinger"])

    def test_local_cycles_are_rejected(self):
        self.write("Hellinger", "module\nimport Hellinger.A\n")
        self.write("Hellinger.A", "module\nimport Hellinger\n")
        with self.assertRaisesRegex(ValueError, "import cycle"):
            verifier.local_import_order(self.root, ["Hellinger", "Hellinger.A"])

    def test_unsupported_import_syntax_fails_closed(self):
        self.write("Hellinger", "module\nimport Hellinger.A Hellinger.B\n")
        with self.assertRaisesRegex(ValueError, "Unsupported import syntax"):
            verifier.local_import_order(self.root, ["Hellinger"])


class AuditParserGuards(unittest.TestCase):
    """Synthetic protocol data tests parsing only; no proof pass is simulated."""
    def setUp(self):
        self.modules = ["Hellinger.Fixture"]
        self.row = {"module": self.modules[0], "name": "ordinary", "axioms": ["propext"],
                    "unsafe": False, "partial": False}
        self.report = {"modules": self.modules, "declarations": [self.row]}

    def output(self):
        return "PROJECT_AXIOM_AUDIT " + json.dumps(self.report) + "\n"

    def check(self):
        return verifier.check_project_axiom_output(self.output(), self.modules, {"ordinary"})

    def test_valid_protocol(self):
        self.assertEqual(self.check(), self.report)

    def test_missing_and_duplicate_reports_are_rejected(self):
        for output in ("", self.output() * 2):
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, "Missing or duplicate"):
                verifier.check_project_axiom_output(output, self.modules, {"ordinary"})

    def test_duplicate_json_key_is_rejected(self):
        output = 'PROJECT_AXIOM_AUDIT {"modules":[],"modules":[],"declarations":[]}\n'
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            verifier.check_project_axiom_output(output, self.modules, {"ordinary"})

    def test_missing_target_and_module_coverage_are_rejected(self):
        for change in ("target", "module"):
            with self.subTest(change=change):
                report = copy.deepcopy(self.report)
                report["declarations"] = [] if change == "target" else report["declarations"]
                report["modules"] = [] if change == "module" else report["modules"]
                with self.assertRaises(ValueError):
                    verifier.check_project_axiom_output("PROJECT_AXIOM_AUDIT " + json.dumps(report),
                                                        self.modules, {"ordinary"})

    def test_unapproved_axiom_on_unused_private_declaration_is_rejected(self):
        extra = copy.deepcopy(self.row)
        extra.update(name="_private.Hellinger.Fixture.0.unused", axioms=["sorryAx"])
        self.report["declarations"].append(extra)
        with self.assertRaisesRegex(ValueError, "Unapproved axioms"):
            self.check()

    def test_unsafe_and_partial_declarations_are_rejected(self):
        for flag in ("unsafe", "partial"):
            with self.subTest(flag=flag):
                self.row[flag] = True
                with self.assertRaisesRegex(ValueError, "Unsafe or partial"):
                    self.check()
                self.row[flag] = False

    def test_duplicate_names_and_foreign_module_are_rejected(self):
        self.report["declarations"].append(copy.deepcopy(self.row))
        with self.assertRaisesRegex(ValueError, "Duplicate project declaration"):
            self.check()
        self.report["declarations"].pop()
        self.row["module"] = "Mathlib.Fixture"
        with self.assertRaisesRegex(ValueError, "unexpected module"):
            self.check()

    def test_boolean_and_axiom_shape_guards(self):
        for field, value in (("unsafe", []), ("partial", 0), ("axioms", "propext"),
                             ("axioms", [None])):
            with self.subTest(field=field, value=value):
                report = copy.deepcopy(self.report)
                report["declarations"][0][field] = value
                with self.assertRaisesRegex(ValueError, "Malformed project declaration audit row"):
                    verifier.check_project_axiom_output("PROJECT_AXIOM_AUDIT " + json.dumps(report),
                                                        self.modules, {"ordinary"})


@unittest.skipUnless(RUN_KERNEL, "pass --kernel to compile adversarial Lean fixtures")
class RealKernelGuards(unittest.TestCase):
    def test_compiled_declarations_use_actual_module_provenance(self):
        lake = verifier.find_lake()
        env = os.environ.copy()
        env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
            env.pop(name, None)
        prefix = subprocess.run([str(lake), "env", "lean", "--print-prefix"], cwd=ROOT,
                                env=env, text=True, capture_output=True, encoding="utf-8")
        self.assertEqual(prefix.returncode, 0, prefix.stdout + prefix.stderr)
        lean = Path(prefix.stdout.strip()) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
        version = subprocess.run([str(lean), "--version"], cwd=ROOT, env=env,
                                 text=True, capture_output=True, encoding="utf-8")
        self.assertEqual(version.returncode, 0, version.stdout + version.stderr)
        self.assertRegex(version.stdout, r"^Lean \(version " + re.escape(verifier.LEAN_VERSION) + ",")
        (ROOT / ".lake").mkdir(exist_ok=True)
        logs, outcomes = [], []
        with tempfile.TemporaryDirectory(prefix="kernel-guards-", dir=ROOT / ".lake") as directory:
            fixture = Path(directory).resolve()
            env["LEAN_PATH"] = str(fixture)
            def run(args):
                result = subprocess.run([str(lean), "--root=" + str(fixture), *args], cwd=fixture,
                                        env=env, text=True, capture_output=True, encoding="utf-8")
                output = result.stdout + result.stderr
                logs.append({"command": [str(lean), *args], "exit_code": result.returncode,
                             "output": output})
                return result.returncode, output
            cases = [
                ("Good", "public theorem ordinary : True := True.intro\n", None),
                ("UnusedAxiom", "public axiom extra : False\npublic theorem ordinary : True := True.intro\n",
                 "Unapproved axioms"),
                ("UnusedSorry", "public theorem unused : False := by sorry\npublic theorem ordinary : True := True.intro\n",
                 "Unapproved axioms"),
                ("PrivateSorry", "private theorem unused : False := by sorry\npublic theorem ordinary : True := True.intro\n",
                 "Unapproved axioms"),
                ("Unsafe", "public unsafe def unchecked : Nat := 0\npublic theorem ordinary : True := True.intro\n",
                 "Unsafe or partial"),
                ("Partial", "public partial def loop (n : Nat) : Nat := loop n\npublic theorem ordinary : True := True.intro\n",
                 "Unsafe or partial"),
                ("NativeDecide", "import Lean.Elab.Tactic.Decide\npublic theorem ordinary : (2 : Nat) + 2 = 4 := by native_decide\n",
                 "Unapproved axioms"),
            ]
            try:
                for name, source, expected in cases:
                    with self.subTest(case=name):
                        module = "VerifierFixture" + name
                        path = fixture / (module + ".lean")
                        path.write_text("module\n" + source, encoding="utf-8", newline="\n")
                        code, output = run(["-o", str(path.with_suffix(".olean")), str(path)])
                        self.assertEqual(code, 0, output)
                        audit = fixture / ("Audit" + name + ".lean")
                        audit.write_text(verifier.project_axiom_audit_source([module]),
                                         encoding="utf-8", newline="\n")
                        code, output = run([str(audit)])
                        self.assertEqual(code, 0, output)
                        if expected:
                            with self.assertRaisesRegex(ValueError, expected):
                                verifier.check_project_axiom_output(output, [module], {"ordinary"})
                            outcomes.append({"case": name, "result": "rejected"})
                        else:
                            report = verifier.check_project_axiom_output(output, [module], {"ordinary"})
                            self.assertTrue(report["declarations"])
                            outcomes.append({"case": name, "result": "permitted"})
                missing = fixture / "MissingModule.lean"
                missing.write_text(verifier.project_axiom_audit_source(["NotCompiled"]), encoding="utf-8")
                code, output = run([str(missing)])
                self.assertNotEqual(code, 0)
                self.assertIn("NotCompiled", output)
                outcomes.append({"case": "missing module", "result": "compiler rejected"})
            finally:
                (ROOT / ".lake" / "kernel-guards.log").write_text(
                    json.dumps(logs, indent=2) + "\n", encoding="utf-8", newline="\n")
                (ROOT / ".lake" / "kernel-guards.json").write_text(
                    json.dumps({"scope": "adversarial Lean fixtures", "outcomes": outcomes}, indent=2)
                    + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    unittest.main(verbosity=2)
