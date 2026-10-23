# Formal proofs of three papers on emissions caps and climate clubs

This repository is a frozen copy of the Lean 4 proofs cited by Appendix B of three papers by Lionel Grenet:

- *A minority-game model of a capped commons: shadow prices, attainable emissions and own impact*.
- *An emissions cap as an admission rule: maximal safe rules, reserves, deadlines and make-up*.
- *Joining a climate club: stable coalitions, safe seeding, supply networks and self-financing*.

Their arXiv identifiers will be added to this file once they are announced; the tagged release cited by the papers does not change.

The 75 files in `ThesePlanetaire/` are copied without change from commit `7ea8c84` of the author's thesis repository: they are the modules that the cited statements import, directly or not. The root file `ThesePlanetaire.lean` is new and imports exactly these modules. Comments in the source files are in French.

## What is claimed

Only the declarations listed below, those cited by Appendix B of the three papers, are claimed as formal counterparts of results of the papers; Appendix B of each paper states the differences between the paper and the formal statements. The other declarations in these files are dependencies or earlier work of the thesis and carry no claim. Some definitions are documentary: in particular, Section 5 of `ThesePlanetaire/EndAnchor.lean` (traces and a conditional Boltzmann measure) is not used by the papers, and the normalisation announced in its comments does not hold for these definitions, since the empty trace is counted in the denominator but not in the numerator.

## Build

Lean `leanprover/lean4:v4.30.0`, Mathlib revision `5719ef27` (`lake-manifest.json`).

```
lake exe cache get
lake build
lake env lean Axioms.lean   # axioms of every cited declaration
```

Every cited declaration depends at most on the axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry` is used.

## Licence

MIT (`LICENSE`). `ThesePlanetaire/FourierMotzkinEconCS.lean` is copied from the EconCSLib library under the Apache License 2.0, with a header and the renaming of an unused argument (`licenses/`).

## Declarations cited by Appendix B, by module

### P12

- `EconCSLib`: `EconCSLib.LinearAlgebra.theorem_of_alternative`
- `GuardSupervisor`: `GuardSupervisor.cast_pureEmit_sum`
- `MeasureFibration`: `MeasureFibration.capFeasible_iff_no_density`, `MeasureFibration.capFeasible_iff_not_cert`, `MeasureFibration.consInst_fiberwise`, `MeasureFibration.exists_H_zero_iff`, `MeasureFibration.load_band`, `MeasureFibration.load_eq`, `MeasureFibration.stockInst_infeasible`, `MeasureFibration.stock_capFeasible_iff`
- `MinorityMeasures`: `MinorityMeasures.attendanceF_eq_load`, `MinorityMeasures.attendance_odd`, `MinorityMeasures.cumF_ge_sum_minLoad`, `MinorityMeasures.eta1_from_aggregate_of_unit`, `MinorityMeasures.eta1_from_recordsF`, `MinorityMeasures.eta1_not_from_aggregateF`, `MinorityMeasures.frozen_cum_linear`, `MinorityMeasures.herd_tradeoffF`, `MinorityMeasures.pair_eta1_cum`
- `MinorityOwnImpact`: `MinorityOwnImpact.eta1_not_from_aggregateN`
- `MinorityWitness`: `MinorityWitness.herd_eta0_periodic`
- `SelfImpactLedger`: `SelfImpactLedger.eta1_from_records`, `SelfImpactLedger.eta1_not_from_aggregate`
- `SoftGate`: `SoftGate.valve_overshoot_ge`

### P11

- `DatedViability`: `DatedViability.effective_date`, `DatedViability.mem_V_iff`, `DatedViability.tenableD_subset_res`
- `DeadlineGuard`: `DeadlineGuard.deferral_strict`, `DeadlineGuard.feasible_mono`, `DeadlineGuard.tokNext_tickOpF`
- `EssentialService`: `EssentialService.greedy_starves_fair`, `EssentialService.resV_necessary`
- `GuardField`: `GuardField.coverage_all_fibers_iff`, `GuardField.fibers_strict`, `GuardField.nb_reserve_necessary`, `GuardField.reachF_iff_run`, `GuardField.reserveF_maximal`, `GuardField.reserveSetF_maximal`, `GuardField.stock_guard_necessaryF`, `GuardField.tickOpF_cast`, `GuardField.tickOpF_le_cap`, `GuardField.tickOpF_tokens`, `GuardField.uncMassF_eq`
- `GuardSupervisor`: `GuardSupervisor.reach_iff_run`
- `JointGuard`: `JointGuard.jointGuard_safe`
- `JointReserve`: `JointReserve.regionJ_iff`, `JointReserve.viableJ_nat_iff`
- `MeasureFibration`: `MeasureFibration.stockInst_infeasible`
- `ReserveCoverage`: `ReserveCoverage.reserveSet_maximal`
- `SoftGate`: `SoftGate.makeup_conservation`
- `TransferCircuit`: `TransferCircuit.guard_simulates`, `TransferCircuit.net_transfer_iff_central`, `TransferCircuit.transfer_not_maximal`

### P15

- `AdhesionEquilibria`: `AdhesionEquilibria.PositiveSpillovers.in_mono`, `AdhesionEquilibria.gfp_greatest_std`, `AdhesionEquilibria.isNashStd_iff_of_ne_zero`, `AdhesionEquilibria.iterate_least_std`, `AdhesionEquilibria.lfp_strict_eq_empty_iff`, `AdhesionEquilibria.lfp_strict_least_std`, `AdhesionEquilibria.payoff_mono_of_subset`, `AdhesionEquilibria.revNet_super`, `AdhesionEquilibria.std_unique_iff`, `AdhesionEquilibria.tie_witness`
- `AdhesionGame`: `AdhesionGame.Supermodular.shift`, `AdhesionGame.afterSeed_nash`, `AdhesionGame.coordGain_super`, `AdhesionGame.gfp_greatest_nash`, `AdhesionGame.ignition_all`, `AdhesionGame.isNash_iff_fixed`, `AdhesionGame.iterate_post`, `AdhesionGame.lfp_eq_empty_iff`, `AdhesionGame.lfp_least_nash`, `AdhesionGame.nash_unique_iff`
- `AdhesionSafety`: `AdhesionSafety.exists_stable_safe_iff`, `AdhesionSafety.not_mem_adh_iff`, `AdhesionSafety.safe_iff`, `AdhesionSafety.safe_mono`, `AdhesionSafety.safety_gap_stock`, `AdhesionSafety.supply_bistable_witness`
- `BasinTarski`: `BasinTarski.basin_fixed_iff`, `BasinTarski.mono_above_012`, `BasinTarski.sym_not_monotone`
- `ClubFinancing`: `ClubFinancing.border_premium_vanishes`, `ClubFinancing.premium_gap_witness`
- `ClubTransfers`: `ClubTransfers.borderFinanced_iff_budget`, `ClubTransfers.club_gain_eq`, `ClubTransfers.premium_gap_internal`
- `ClubWelfare`: `ClubWelfare.club_netGain_club`, `ClubWelfare.club_spillovers_iff`, `ClubWelfare.exists_nash_iff_of_upward`, `ClubWelfare.stick_super`
- `JointReserve`: `JointReserve.viableC_iff`
- `JointSafety`: `JointSafety.critical_two_caps`, `JointSafety.exists_stable_jsafe_iff`, `JointSafety.exists_stable_jsafe_iff_forall`, `JointSafety.jsafe_iff_forall_safe`
- `ReserveCoverage`: `ReserveCoverage.coverage_stock_iff`
- `RobustIgnition`: `RobustIgnition.coord_tipping`, `RobustIgnition.robust_iff_margin`
- `SupplyPropagation`: `SupplyPropagation.down_only_emitters`, `SupplyPropagation.feasible_not_propagated`
- `ViabilityKernel`: `ViabilityKernel.viability_kernel_eq_gfp`
