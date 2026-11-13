"""
Syntax and Proof Obligation Verifier for Alpha Coq files (00.v, alpha_core.v).
Provides static AST and delimiter verification, and optional coqc compilation when present.
"""

from __future__ import annotations
import os
import re
import shutil
import subprocess
from typing import Dict, List, Optional, Tuple


class CoqVerifier:
    """Verifies Coq formal development files in Alpha."""

    def __init__(self, filepath: str):
        self.filepath = filepath
        if not os.path.isfile(filepath):
            raise FileNotFoundError(f"Coq file not found: {filepath}")
        with open(filepath, "r", encoding="utf-8") as f:
            self.content = f.read()

    def check_balanced_comments(self) -> bool:
        """Verifies that nested Coq comments (* ... *) are balanced."""
        depth = 0
        i = 0
        n = len(self.content)
        while i < n - 1:
            if self.content[i : i + 2] == "(*":
                depth += 1
                i += 2
            elif self.content[i : i + 2] == "*)":
                depth -= 1
                if depth < 0:
                    return False
                i += 2
            else:
                i += 1
        return depth == 0

    def check_balanced_sections(self) -> Tuple[bool, List[str]]:
        """Verifies that Section names match End statements."""
        sections: List[str] = []
        errors: List[str] = []

        lines = self.content.splitlines()
        for line in lines:
            # Strip comments approximately
            cleaned = re.sub(r"\(\*.*?\*\)", "", line).strip()
            sec_match = re.match(r"^Section\s+([A-Za-z0-9_]+)\s*\.", cleaned)
            if sec_match:
                sections.append(sec_match.group(1))

            end_match = re.match(r"^End\s+([A-Za-z0-9_]+)\s*\.", cleaned)
            if end_match:
                end_name = end_match.group(1)
                if not sections:
                    errors.append(f"Unexpected End {end_name} without matching Section")
                else:
                    last_sec = sections.pop()
                    if last_sec != end_name:
                        errors.append(f"Mismatched End {end_name}, expected End {last_sec}")

        if sections:
            errors.append(f"Unclosed sections: {sections}")

        return (len(errors) == 0, errors)

    def find_deprecated_tactics(self) -> List[str]:
        """Detects deprecated Coq tactics such as Omega."""
        found = []
        if re.search(r"\bRequire\s+Import\s+Omega\b", self.content):
            found.append("Require Import Omega (deprecated; use Coq.micromega.Lia)")
        if re.search(r"\bomega\b", self.content):
            found.append("omega tactic used (deprecated; use lia)")
        return found

    def find_obligations(self) -> List[str]:
        """Identifies Program Fixpoint obligations in the Coq file."""
        obligations = re.findall(r"Next\s+Obligation\b.*?(?:Defined|Qed|Admitted)\.", self.content, re.DOTALL)
        return obligations

    def find_lemmas(self) -> List[str]:
        """Returns the list of Lemma and Theorem names in the file."""
        return re.findall(r"\b(?:Lemma|Theorem)\s+([A-Za-z0-9_]+)\s*:", self.content)

    def check_explicit_type_annotations(self) -> Tuple[bool, List[str]]:
        """
        Verifies that all forall-quantified variables in lemmas and theorems
        contain explicit type annotations (e.g. `(x : var)` rather than unannotated `x`).
        """
        errors: List[str] = []
        lemma_pattern = re.compile(
            r"\b(?:Lemma|Theorem)\s+([A-Za-z0-9_]+)\s*:\s*(.*?)\.\s*Proof\b",
            re.DOTALL,
        )
        for match in lemma_pattern.finditer(self.content):
            lemma_name = match.group(1)
            statement = match.group(2)
            # Check forall clauses in lemma statement
            for forall_match in re.finditer(r"\bforall\s+([^,]+),", statement):
                binder_group = forall_match.group(1).strip()
                if not binder_group.startswith("(") or ":" not in binder_group:
                    errors.append(
                        f"Lemma/Theorem {lemma_name} has unannotated or non-standard binder: 'forall {binder_group},'"
                    )
        return (len(errors) == 0, errors)

    def verify_with_compiler(self) -> Tuple[bool, str]:
        """Runs coqc on the file if coqc is installed."""
        coqc_path = shutil.which("coqc")
        if not coqc_path:
            return (True, "coqc not present in environment; skipped external compile check")
        proc = subprocess.run(
            [coqc_path, "-q", self.filepath],
            capture_output=True,
            text=True,
        )
        if proc.returncode == 0:
            return (True, "coqc compilation succeeded")
        else:
            return (False, f"coqc compilation failed:\n{proc.stderr}")
