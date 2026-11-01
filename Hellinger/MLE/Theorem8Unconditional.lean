/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Theorem8
public import Hellinger.VdW.Main

/-!
Corrected Theorem 8 and its corollaries, unconditionally. The maximal inequality
`External.VdW_2_14_18_prime` (van der Vaart and Wellner 2023, Theorem 2.14.18') is proved as
`External.vdw_2_14_18_prime` (`Hellinger/VdW/Main.lean`); each theorem here applies the
corresponding theorem of `Theorem8.lean` to that proof.
-/

@[expose] public section

namespace Hellinger.MLE

universe u v

/-- **Corrected Theorem 8** under the annular entropy-tail condition (D). -/
theorem theorem8_unconditional : Theorem8Statement.{u, v} :=
  theorem8 External.vdw_2_14_18_prime

/-- The ordinary `O_P` form when the Hellinger error is measurable. -/
theorem theorem8_measurable_unconditional : Theorem8MeasurableStatement.{u, v} :=
  theorem8_measurable External.vdw_2_14_18_prime

/-- The rate theorem under the power envelope (H). -/
theorem theorem8_of_powerEnvelope_unconditional : Theorem8PowerEnvelopeStatement.{u, v} :=
  theorem8_of_powerEnvelope External.vdw_2_14_18_prime

/-- The rate theorem under the whole-sieve bound (G). -/
theorem theorem8_of_wholeSieve_unconditional : Theorem8WholeSieveStatement.{u, v} :=
  theorem8_of_wholeSieve External.vdw_2_14_18_prime

end Hellinger.MLE
