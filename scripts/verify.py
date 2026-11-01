# Copyright 2026 Tetsuya Kaji
# SPDX-License-Identifier: Apache-2.0
"""Verify the frozen source snapshot, dependency pins, exports, and Lean axioms.

Run with Python 3.10 or later after installing the pinned Lean toolchain and
fetching the Lake dependencies and mathlib cache. Only the standard library is
used. Commands and compiler output are saved under .lake/verification.log.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys

ARTICLE_DOI = "10.1007/s42973-026-00243-x"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0"
LEAN_VERSION = "4.35.0"
VERSION = "0.1.0"
MODULE_COUNT = 88
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DEPENDENCY_PINS = {
    "mathlib": "56a005855ea17e0b0958f73ec801ae140b0a1679",
    "plausible": "dfa4f38190d07c37e315953e08b90fe2d95b3c24",
    "LeanSearchClient": "d6b4c7be5be75ec4917c873ac50c756dc1436372",
    "importGraph": "a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93",
    "proofwidgets": "df72b022e558978a1c50264cfc4d7fec86fa8e04",
    "aesop": "4a174c490d8707121c4a9290800489f105d85e07",
    "Qq": "dce0ad79c486cb1fb504af04f953c3466b0c6db8",
    "batteries": "66e469188fe07963e5cf666c7d4433f45b8131c5",
    "Cli": "c24fe6078c630e89b489bffe59b3e20ac30d12c8",
}
MAIN_DECLARATIONS = {
    "Hellinger.bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq",
    "Hellinger.bernsteinSq_le_hellinger_add_tailPower",
    "Hellinger.hellingerSq_le_kl",
    "Hellinger.kl_le_hellinger_add_tailPower",
    "Hellinger.two_neg_rpow_mul_centeredLogMoment_le_logMoment",
    "Hellinger.logMoment_le_gamma_bernsteinSq",
    "Hellinger.klTailLowerCoeff_mul_tailLogMoment_le_kl",
    "Hellinger.kl_le_hellinger_add_tailLogMoment",
    "Hellinger.tailLogMoment_le_logMoment",
    "Hellinger.logMoment_le_hellinger_add_tailLogMoment",
    "Hellinger.tailLogMoment_interpolation",
    "Hellinger.uniform_bernsteinSq_iff_tailPower",
    "Hellinger.uniform_kl_iff_tailLogMoment",
    "Hellinger.uniform_logMoment_iff_tailLogMoment",
    "Hellinger.Comparison.tailPower_mono_exponent",
    "Hellinger.Comparison.tailPower_interpolation",
    "Hellinger.Comparison.uniform_tailPower_of_larger_exponent",
    "Hellinger.Comparison.Examples.Power.power_density_separation",
    "Hellinger.uniform_ws_iff_tailPower",
    "Hellinger.Comparison.tailLogMoment_le_of_ws",
    "Hellinger.Comparison.kl_and_logMoment_le_of_ws",
    "Hellinger.Comparison.tailPower_one_le_of_conditionalMoment_le",
    "Hellinger.Comparison.conditionalMoment_lt_top_of_tailPower_one_lt_top",
    "Hellinger.Comparison.Examples.CMSeparation.cm_family_separation",
    "Hellinger.Comparison.uniform_conditionalMoment_of_uniform_ratio_representative_bound",
    "Hellinger.Comparison.Examples.Normal.normal_location_fails_ub",
    "Hellinger.Comparison.Examples.Normal.uniform_conditionalMoment_normalFamily",
    "Hellinger.Comparison.uniform_fullRatioMoment_of_uniform_tailPower_one",
    "Hellinger.Comparison.fullRatioMoment_le_tailPower_add_sqrt_hellinger",
    "Hellinger.Comparison.Examples.Power.fractional_nc_without_full_moment",
    "Hellinger.Comparison.Examples.FMSeparation.fm_family_separation",
    "Hellinger.Comparison.Summary.forward_implications",
    "Hellinger.MLE.theorem8_unconditional",
    "Hellinger.MLE.theorem8_of_powerEnvelope_unconditional",
    "Hellinger.MLE.theorem8_of_wholeSieve_unconditional",
    "Hellinger.MLE.External.vdw_2_14_18_prime",
    "Hellinger.MLE.theorem8_weakLaw_unconditional",
    "Hellinger.MLE.theorem8_firstMoment_unconditional",
    "Hellinger.MLE.theorem8_of_weakLaw",
    "Hellinger.MLE.nonvacuous_nondegenerate",
    "Hellinger.Sharp.kl_le_hellinger_add_tailLogMoment_sharp",
    "Hellinger.Sharp.kl_le_hellinger_add_tailPower_sharp",
    "Hellinger.Sharp.klTailLowerSharpCoeff_mul_tailLogMoment_le_kl",
    "Hellinger.Sharp.bernsteinLowerSharpCoeff_mul_tailPower_le_bernsteinSq",
    "Hellinger.Sharp.bernsteinSq_le_hellinger_add_tailPower_sq",
    "Hellinger.Sharp.logMoment_le_hellinger_add_tailLogMoment_sharp",
    "Hellinger.Sharp.tailLogMoment_interpolation_sharp",
    "Hellinger.Sharp.tailPower_le_of_conditionalMoment_le_sharp",
    "Hellinger.Sharp.sharpCoeffs_improve",
}
MODULE_PATTERN = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"
DECLARATION_PATTERN = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
IGNORED_DIRECTORIES = {".git", ".lake", "__pycache__"}
GENERATED_FILES = {"snapshot.json", "verification.json"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json(text: str) -> object:
    def invalid_constant(value: str) -> None:
        raise ValueError(f"Invalid JSON constant: {value}")
    return json.loads(text, object_pairs_hook=unique_object,
                      parse_constant=invalid_constant)


def read_json(path: Path) -> object:
    return parse_json(path.read_text(encoding="utf-8"))


def local(root: Path, relative: str) -> Path:
    """Accept canonical portable relative paths, never traversal or symlinks."""
    require(isinstance(relative, str) and bool(relative), "Empty snapshot path")
    parts = PurePosixPath(relative).parts
    require(not PurePosixPath(relative).is_absolute()
            and "\\" not in relative and ":" not in relative
            and all(part not in {"", ".", ".."} for part in relative.split("/"))
            and str(PurePosixPath(relative)) == relative,
            f"Noncanonical snapshot path: {relative}")
    path = root.joinpath(*parts)
    require(path.resolve().is_relative_to(root.resolve()),
            f"Path escapes project: {relative}")
    current = root
    for part in parts:
        current = current / part
        require(not current.is_symlink(), f"Symlink is not a snapshot file: {relative}")
    return path


def distributable_files(root: Path) -> set[str]:
    files = set()
    def walk_error(_error: OSError) -> None:
        raise ValueError("Cannot enumerate snapshot files")
    for directory, subdirs, names in os.walk(root, onerror=walk_error):
        subdirs[:] = sorted(name for name in subdirs if name not in IGNORED_DIRECTORIES)
        for name in subdirs:
            relative = (Path(directory) / name).relative_to(root).as_posix()
            require(not local(root, relative).is_symlink(),
                    f"Symlink is not a snapshot directory: {relative}")
        for name in names:
            relative = (Path(directory) / name).relative_to(root).as_posix()
            if relative in GENERATED_FILES:
                continue
            require(local(root, relative).is_file(), f"Not a regular file: {relative}")
            files.add(relative)
    return files


def verify_snapshot(root: Path, expected: dict | None = None) -> dict:
    snapshot = read_json(local(root, "snapshot.json"))
    require(isinstance(snapshot, dict) and set(snapshot) == {"schema_version", "version", "files"},
            "Malformed snapshot manifest")
    require(type(snapshot["schema_version"]) is int and snapshot["schema_version"] == 1
            and snapshot["version"] == VERSION, "Unsupported snapshot version")
    hashes = snapshot["files"]
    require(isinstance(hashes, dict) and bool(hashes), "Empty snapshot file inventory")
    for relative, sha in hashes.items():
        local(root, relative)
        require(relative not in GENERATED_FILES
                and not (set(PurePosixPath(relative).parts) & IGNORED_DIRECTORIES),
                f"Excluded path in snapshot: {relative}")
        require(isinstance(sha, str) and re.fullmatch(r"[0-9A-F]{64}", sha) is not None,
                f"Malformed SHA256: {relative}")
    required = {"lean-toolchain", "lake-manifest.json", "lakefile.toml", "Hellinger.lean",
                "declarations.json", "scripts/verify.py"}
    require(required <= set(hashes), "Snapshot omits required package files")
    actual = distributable_files(root)
    require(set(hashes) == actual,
            "Snapshot file inventory differs: missing=" + ", ".join(sorted(set(hashes) - actual))
            + "; unlisted=" + ", ".join(sorted(actual - set(hashes))))
    for relative, sha in hashes.items():
        require(digest(local(root, relative)) == sha, f"Snapshot hash mismatch: {relative}")
    if expected is not None:
        require(snapshot == expected, "Snapshot manifest changed during verification")
    return snapshot


def check_declarations(data: object) -> tuple[list[dict], set[str]]:
    require(isinstance(data, dict) and set(data) == {"schema_version", "article_doi", "results"},
            "Malformed declaration map")
    require(type(data["schema_version"]) is int and data["schema_version"] == 1
            and data["article_doi"] == ARTICLE_DOI, "Declaration map provenance mismatch")
    results = data["results"]
    require(isinstance(results, list) and len(results) == len(MAIN_DECLARATIONS),
            "Principal declaration inventory changed")
    keys, main, names = set(), set(), set()
    for row in results:
        require(isinstance(row, dict) and set(row) == {
            "key", "paper", "title", "declaration", "related_declarations"},
            "Malformed declaration entry")
        key = row["key"]
        require(isinstance(key, str) and re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", key) is not None,
                "Malformed public result key")
        require(key not in keys, "Duplicate public result key")
        keys.add(key)
        require(all(isinstance(row[field], str) and bool(row[field].strip())
                    for field in ("paper", "title")), "Missing paper locator or result title")
        declaration = row["declaration"]
        related = row["related_declarations"]
        require(isinstance(related, list) and all(isinstance(name, str) for name in related),
                "Malformed related declaration inventory")
        require(len(related) == len(set(related)), "Duplicate related declaration")
        require(isinstance(declaration, str) and all(
            re.fullmatch(DECLARATION_PATTERN, name) is not None
            for name in [declaration, *related]), "Malformed Lean declaration name")
        require(declaration not in main, "Duplicate principal declaration")
        main.add(declaration)
        names.update([declaration, *related])
    require(main == MAIN_DECLARATIONS, "Principal declaration inventory changed")
    return results, names


def project_modules(artifacts: set[str]) -> list[str]:
    modules = []
    for path in sorted(artifacts):
        if not path.endswith(".lean") or path == "lakefile.lean":
            continue
        module = path[:-5].replace("/", ".")
        require(re.fullmatch(MODULE_PATTERN, module) is not None,
                f"Unsupported local Lean module path: {path}")
        require(module == "Hellinger" or module.startswith("Hellinger."),
                f"Module is outside the Hellinger library: {module}")
        modules.append(module)
    require(len(modules) == MODULE_COUNT and "Hellinger" in modules,
            "Local Lean module inventory changed")
    return modules


def strip_comments_and_strings(source: str) -> str:
    """Preserve newlines while masking Lean's nested comments and strings."""
    output, index, depth, string = [], 0, 0, False
    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif string:
            if char == "\\" and index + 1 < len(source):
                output.extend("\n" if value == "\n" else " " for value in source[index:index + 2])
                index += 2
            else:
                if char == '"':
                    string = False
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "--":
            stop = source.find("\n", index)
            if stop == -1:
                stop = len(source)
            output.extend(" " * (stop - index))
            index = stop
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    require(not depth and not string, "Unterminated Lean comment or string")
    return "".join(output)


def local_import_order(root: Path, modules: list[str]) -> list[str]:
    """Build one local target at a time after all its local imports are built."""
    module_set, dependencies = set(modules), {}
    pattern = re.compile(r"\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?(" + MODULE_PATTERN + r")\s*")
    for module in modules:
        path = local(root, module.replace(".", "/") + ".lean")
        source = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        dependencies[module] = set()
        for line in source.splitlines():
            if re.match(r"\s*(?:(?:public|private)\s+)?import\b", line):
                match = pattern.fullmatch(line)
                require(match is not None, f"Unsupported import syntax in {module}")
                imported = match.group(1)
                if imported == "Hellinger" or imported.startswith("Hellinger."):
                    require(imported in module_set, f"Missing local import: {imported}")
                    dependencies[module].add(imported)
    order, visited, active = [], set(), set()
    def visit(module: str) -> None:
        require(module not in active, f"Local import cycle: {module}")
        if module in visited:
            return
        active.add(module)
        for dependency in sorted(dependencies[module]):
            visit(dependency)
        active.remove(module)
        visited.add(module)
        order.append(module)
    for module in modules:
        visit(module)
    return order


def project_axiom_audit_source(modules: list[str]) -> str:
    """Use Lean's environment/module provenance and transitive axiom collector.

    Import private data explicitly so unused private declarations are checked
    too. Namespace prefixes and source-text scans are not proof/trust checks.
    """
    require(bool(modules) and all(re.fullmatch(
        r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", m) for m in modules),
        "Malformed project module name")
    imports = "\n".join("import all " + m for m in modules)
    module_strings = ", ".join(json.dumps(m) for m in modules)
    return f'''module
import Lean
{imports}
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let projectModules : Array String := #[{module_strings}]
  for mod in projectModules do
    unless env.allImportedModuleNames.any (fun n => n.toString == mod) do
      throwError "Local module missing from checked environment: {{mod}}"
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some mod := env.allImportedModuleNames[idx]? then
        if projectModules.contains mod.toString then
          let axioms ← collectAxioms name
          rows := rows.push <| Json.mkObj [
            ("module", toJson mod.toString), ("name", toJson name.toString),
            ("axioms", toJson (axioms.map Name.toString)),
            ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial)]
  liftIO <| IO.println ("PROJECT_AXIOM_AUDIT " ++
    (Json.mkObj [("modules", toJson projectModules), ("declarations", toJson rows)]).compress)
'''


def check_project_axiom_output(output: str, modules: list[str], targets: set[str]) -> dict:
    lines = [line.removeprefix("PROJECT_AXIOM_AUDIT ") for line in output.splitlines()
             if line.startswith("PROJECT_AXIOM_AUDIT ")]
    require(len(lines) == 1, "Missing or duplicate project axiom audit report")
    report = parse_json(lines[0])
    require(isinstance(report, dict) and set(report) == {"modules", "declarations"},
            "Malformed project axiom audit report")
    require(report["modules"] == modules, "Project axiom audit module coverage mismatch")
    rows = report["declarations"]
    require(isinstance(rows, list), "Malformed project declaration audit")
    for row in rows:
        require(isinstance(row, dict) and set(row) == {"module", "name", "axioms", "unsafe", "partial"}
                and isinstance(row["module"], str) and isinstance(row["name"], str) and bool(row["name"])
                and isinstance(row["axioms"], list)
                and all(isinstance(name, str) and bool(name) for name in row["axioms"])
                and type(row["unsafe"]) is bool and type(row["partial"]) is bool,
                "Malformed project declaration audit row")
    names = [row["name"] for row in rows]
    require(len(names) == len(set(names)), "Duplicate project declaration in axiom audit")
    require(targets <= set(names), "Mapped target missing from local declaration audit")
    for row in rows:
        require(row["module"] in modules, "Axiom audit contains an unexpected module")
        require(not row["unsafe"] and not row["partial"],
                f"Unsafe or partial project declaration: {row['name']}")
        used = set(row["axioms"])
        require(used <= ALLOWED_AXIOMS,
                f"Unapproved axioms for {row['name']}: {used - ALLOWED_AXIOMS}")
    return report


def find_lake() -> Path:
    executable = shutil.which("lake")
    if executable:
        # Preserve elan's executable name when the launcher is a symlink.
        return Path(os.path.abspath(executable))
    fallback = Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    require(fallback.is_file(), "Lake is unavailable; install elan and the pinned toolchain")
    return fallback


class Runner:
    def __init__(self, root: Path, env: dict[str, str]):
        self.root, self.env = root, env
        self.log = root / ".lake" / "verification.log"
        self.log.parent.mkdir(parents=True, exist_ok=True)
        self.log.write_text("", encoding="utf-8", newline="\n")

    def try_run(self, command: list[str], label: str) -> tuple[int, str]:
        completed = subprocess.run(command, cwd=self.root, env=self.env, capture_output=True,
                                   text=True, encoding="utf-8", errors="replace")
        output = completed.stdout + completed.stderr
        with self.log.open("a", encoding="utf-8", newline="\n") as log:
            log.write(json.dumps({"step": label, "command": command,
                                  "exit_code": completed.returncode,
                                  "output": output}, ensure_ascii=False) + "\n")
        return completed.returncode, output

    def run(self, command: list[str], label: str) -> str:
        code, output = self.try_run(command, label)
        require(code == 0, f"{label} failed; see .lake/verification.log")
        return output


def verify_dependency_pins(root: Path, runner: Runner) -> dict:
    require((root / "lean-toolchain").read_text(encoding="utf-8").strip() == LEAN_TOOLCHAIN,
            "Lean toolchain pin mismatch")
    manifest = read_json(root / "lake-manifest.json")
    require(isinstance(manifest, dict) and isinstance(manifest.get("packages"), list),
            "Malformed Lake dependency manifest")
    require(manifest.get("packagesDir") == ".lake/packages", "Unexpected dependency directory")
    packages = manifest["packages"]
    require(all(isinstance(package, dict) and isinstance(package.get("name"), str)
                for package in packages), "Malformed dependency entry")
    names = [package["name"] for package in packages]
    require(len(names) == len(set(names)) and set(names) == set(DEPENDENCY_PINS),
            "Dependency package inventory changed")
    results = {}
    for package in packages:
        name = package["name"]
        require(package.get("type") == "git" and package.get("rev") == DEPENDENCY_PINS[name]
                and package.get("subDir") is None, f"Dependency pin mismatch: {name}")
        # The ignored dependency cache may be shared through a filesystem link.
        # The fixed package names and each resolved repository's pins and clean
        # source, rather than its machine-specific location, are authenticated.
        dependency = root / ".lake" / "packages" / name
        require(dependency.is_dir(), f"Missing dependency: {name}; run lake update first")
        top = runner.run(["git", "-C", str(dependency), "rev-parse", "--show-toplevel"],
                         f"Dependency repository {name}").strip()
        require(Path(top).resolve() == dependency.resolve(), f"Not a dependency repository: {name}")
        head = runner.run(["git", "-C", str(dependency), "rev-parse", "HEAD"],
                          f"Dependency revision {name}").strip()
        require(head == package["rev"], f"Dependency revision mismatch: {name}")
        dirty = runner.run(["git", "-C", str(dependency), "status", "--porcelain",
                            "--untracked-files=normal"], f"Dependency cleanliness {name}").strip()
        require(not dirty, f"Dirty dependency source: {name}")
        results[name] = {"revision": head, "clean": True}
    return results


def verify(root: Path, write_report: bool = True) -> dict:
    snapshot = verify_snapshot(root)
    snapshot_sha = digest(root / "snapshot.json")
    results, targets = check_declarations(read_json(root / "declarations.json"))
    modules = project_modules(set(snapshot["files"]))
    order = local_import_order(root, modules)
    print(f"Snapshot verified: {len(snapshot['files'])} files, {len(modules)} Lean modules", flush=True)
    lake = find_lake()
    env = os.environ.copy()
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
    # Lake supplies the package search path. Inherited overrides must not select
    # a different standard library or add unrelated compiled modules.
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(name, None)
    runner = Runner(root, env)
    pins = verify_dependency_pins(root, runner)
    version = runner.run([str(lake), "env", "lean", "--version"], "Lean version")
    require(re.match(r"Lean \(version " + re.escape(LEAN_VERSION) + r"(?:,|\))", version) is not None,
            "Running Lean version differs from the toolchain pin")
    print(f"Dependency pins verified: {len(pins)} clean Git packages", flush=True)
    # Lake's --no-build checks every target without starting missing builds.
    # A warm snapshot avoids repeatedly loading Lake's package configuration.
    # A cold snapshot builds in local dependency order, one target per command.
    code, _ = runner.try_run([str(lake), "--no-build", "build",
                              *("+" + module + ":olean" for module in modules)],
                             "Check all local build targets are current")
    build_mode = "up_to_date" if code == 0 else "serial"
    if code == 0:
        print(f"All {len(modules)} local build targets are current", flush=True)
    else:
        for index, module in enumerate(order, 1):
            print(f"Building {index}/{len(order)}: {module}", flush=True)
            runner.run([str(lake), "build", "+" + module + ":olean"], "Build " + module)
    public_path = root / ".lake" / "PublicTargets.lean"
    public_path.write_text("import Hellinger\n" + "\n".join(
        "#check " + name for name in sorted(targets)) + "\n", encoding="utf-8", newline="\n")
    runner.run([str(lake), "env", "lean", str(public_path)], "Public declaration checks")
    audit_path = root / ".lake" / "ExportAxioms.lean"
    audit_path.write_text(project_axiom_audit_source(modules), encoding="utf-8", newline="\n")
    print("Auditing every local declaration, including private and unused declarations", flush=True)
    output = runner.run([str(lake), "env", "lean", str(audit_path)], "Local declaration axiom audit")
    audit = check_project_axiom_output(output, modules, targets)
    (root / ".lake" / "project-axioms.json").write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    require(verify_dependency_pins(root, runner) == pins, "Dependencies changed during verification")
    verify_snapshot(root, snapshot)
    require(digest(root / "snapshot.json") == snapshot_sha,
            "Snapshot manifest bytes changed during verification")
    used_axioms = sorted({axiom for row in audit["declarations"] for axiom in row["axioms"]})
    report = {
        "schema_version": 1, "version": VERSION, "article_doi": ARTICLE_DOI, "status": "pass",
        "snapshot_sha256": snapshot_sha, "artifact_hashes": snapshot["files"],
        "toolchain": LEAN_TOOLCHAIN, "dependency_pins": pins,
        "modules": modules, "build_order": order, "build_mode": build_mode,
        "local_declaration_count": len(audit["declarations"]),
        "permitted_axioms": sorted(ALLOWED_AXIOMS), "used_axioms": used_axioms,
        "coverage": {"principal_results": len(results), "checked_declarations": len(targets),
                     "declarations": sorted(targets), "all_local_modules": True,
                     "private_and_unused_declarations": True, "public_root_checks": True},
        "snapshot_unchanged": True,
    }
    if write_report:
        (root / "verification.json").write_text(json.dumps(report, indent=2) + "\n",
                                               encoding="utf-8", newline="\n")
    print(f"VERIFICATION PASS: {len(results)} results, {len(targets)} checked exports, "
          f"{len(audit['declarations'])} local declarations; only permitted axioms", flush=True)
    return report


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-report", action="store_true", help="do not write verification.json")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    # Never leave an older successful report after a failed invocation.
    report_path = root / "verification.json"
    try:
        require(not report_path.is_symlink(), "verification.json must not be a symlink")
        report_path.unlink(missing_ok=True)
        verify(root, write_report=not args.no_report)
    except (ValueError, KeyError, TypeError, OSError, RecursionError) as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
