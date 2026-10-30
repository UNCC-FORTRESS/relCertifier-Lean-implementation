## Matrix

| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ widened cut | M6L linear-form chain | M7 scenario; dim; invariant; domains |
|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | CERTIFIED (139) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=2 via CRUISE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 2; conjunctive |
| `acc_spoof_limp` | CERTIFIED (184) | no (λ=1 everywhere) | yes: CRUISE B=2 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT | yes: CRUISE branch=2, LIMP branch=2 | vacuous: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE... | no (rows identical; handoff vacuous) | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `acc_tune_lag` | CERTIFIED (168) | yes: CRUISE λ=2 (affine dynamics) | yes: CRUISE B=2 via CRUISE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-controller; dim 2; conjunctive |
| `acc_tune_limp` | CERTIFIED (614) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=2 via NORMAL | no (max non-self successors at a joint step = 0) | vacuous: pruned NORMAL->DISENGAGE but NO_PRUNE=CERTIFIED | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | no (no linear-form atom kept) | degraded-controller; dim 1; conjunctive+linear |
| `antenna_track_kvretune` | CERTIFIED (898) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 6/6 handoffs unsat, rows differ | vacuous: cuts kept (L.TRACK: 4 conjunct(s); L.STOW: 3 conjunct(s); ... | no (no widened atom kept) | no (no linear-form atom kept) | controller-change; dim 3; conjunctive |
| `bottling_fill_strainer` | CERTIFIED (571) | yes: FILL λ=17/20 (affine dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.FILL: 4 conjunct(s); L.CLOSE: 4 conjunct(s); R.FILL: 4 conju... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `canal_gate_notches` | CERTIFIED (317) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.RAISE: 2 conjunct(s); L.HOLD: 2 conjunct(s); ... | vacuous: widened atoms kept (L.RAISE: h <= 0.95 kind=implied-contra... | no (no linear-form atom kept) | controller-refinement; dim 1; conjunctive |
| `elevator_start_discbrake` | CERTIFIED (990) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 7/7 handoffs unsat, rows differ | vacuous: cuts kept (L.LIFT: 8 conjunct(s); L.UP: 6 conjunct(s); L.A... | no (no widened atom kept) | no (no linear-form atom kept) | actuator-change; dim 3; conjunctive |
| `engine_start_highidle` | CERTIFIED (743) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 12/12 handoffs unsat, rows differ | yes: L.STARTER: 3 conjunct(s); L.STARTER_LOW: 3 conjunct(s); L.LIGH... | yes: L.STARTER: n <= 30 kind=implied-contraction entry=rational rou... | no (no linear-form atom kept) | controller-change; dim 3; conjunctive+linear |
| `flaps_slow_approach` | CERTIFIED (303) | yes: EXT λ=1/2 (polynomial dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.EXT: 3 conjunct(s); L.CONF2: 5 conjunct(s); R... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `fuelcell_chp_dos` | CERTIFIED (463) | no (λ=1 everywhere) | yes: LOW B=2 via LOW +choice MED:hop, MED B=2 via HIGH/LOW/MED, HIG... | yes: MED branch=2 | yes: pruned LOW->HIGH, HIGH->LOW; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.LOW: 5 conjunct(s); L.MED: 5 conjunct(s); L.HIGH: 5 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `furnace_program_timebase` | CERTIFIED (1132) | yes: PREHEAT λ=4/5, HEAT λ=4/5, SOAK λ=4/5 (affine dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.PREHEAT: 3 conjunct(s); L.HEAT: 4 conjunct(s); L.SOAK: 4 con... | yes: L.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational ... | no (no linear-form atom kept) | controller-change; dim 2; conjunctive |
| `gantry_speed_zones` | CERTIFIED (1250) | yes: FREE λ=3, APPROACH λ=2 (affine dynamics) | yes: FREE B=3 via MOVE, APPROACH B=2 via MOVE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.FREE: 4 conjunct(s); L.APPROACH: 4 conjunct(s... | vacuous: widened atoms kept (L.FREE: x <= 0.5 kind=implied-contract... | no (no linear-form atom kept) | controller-refinement; dim 2; conjunctive |
| `h2_refuel_ambientbias` | CERTIFIED (617) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 9/9 handoffs unsat, rows differ | yes: L.STAGE1: 1 conjunct(s); L.STAGE2: 2 conjunct(s); L.STAGE3: 2 ... | yes: L.STAGE1: p <= 20 kind=implied-contraction entry=rational rout... | no (no linear-form atom kept) | sensor-fault (degraded sensor feeding the end-pressure table); dim 1; conjunctive+linear |
| `hydro_rejection_gatecal` | CERTIFIED (312) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | vacuous: cuts kept (L.ONGRID: 5 conjunct(s); L.REJECT: 6 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 3; conjunctive |
| `lit_csf21_vehicle_bus` | CERTIFIED (3275) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 3; conjunctive |
| `lit_csf21_vehicle_thermo` | CERTIFIED (1756) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 3; conjunctive |
| `lit_csf25_salt_tank_hold` | CERTIFIED (294) | yes: HoldInc λ=1/3, HoldDec λ=1/3 (affine dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 2/2 handoffs unsat, rows differ | yes: L.HoldInc: 3 conjunct(s); L.HoldDec: 3 conjunct(s); R.Inc: 1 c... | yes: L.HoldInc: xp >= 36.43 kind=closure entry=weakening route=shap... | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `lit_drl_lane_control` | CERTIFIED (2670) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccelLAccel: 2 conjunct(s); L.AccelLBrake: 2 ... | no (no widened atom kept) | no (no linear-form atom kept) | controller-refinement; dim 3; conjunctive |
| `lit_freedm_meter` | CERTIFIED (2292) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.BatD0R0: 2 conjunct(s); L.BatD0R1: 1 conjunct... | vacuous: widened atoms kept (L.BatD0R0: B <= 10.0 kind=closure entr... | no (no linear-form atom kept) | information-flow; dim 2; conjunctive |
| `lit_girard08_robot` | CERTIFIED (53551) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (R.M1: 2 conjunct(s); R.M2: 1 conjunct(s); R.M3:... | no (no widened atom kept) | no (no linear-form atom kept) | abstraction; dim 6+-4; quadratic+conj |
| `lit_gpt10_boost_converter` | CERTIFIED (50932) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.P1d00: 1 conjunct(s); L.P1d01: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | abstraction; dim 2; quadratic |
| `lit_lz21_vehicle_position` | CERTIFIED (413) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Um: 1 conjunct(s); L.U0: 2 conjunct(s); L.Up:... | no (no widened atom kept) | no (no linear-form atom kept) | opacity; dim 2; conjunctive |
| `lit_nahs25_salt_tank` | CERTIFIED (197) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.On: 1 conjunct(s); L.Off: 1 conjunct(s); R.On... | vacuous: widened atoms kept (L.Off: xp <= 28.0 kind=closure entry=w... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `molding_pack_checkring` | CERTIFIED (398) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | vacuous: cuts kept (L.HOLD: 3 conjunct(s); L.COOL: 4 conjunct(s); R... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 3; conjunctive |
| `platoon_latency` | CERTIFIED (395) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (R.CACC: 4 conjunct(s)) but NO_CUT=CERTIFIED | no (no widened atom kept) | no (no linear-form atom kept) | degraded-network; dim 3; conjunctive |
| `platoon_linkloss` | CERTIFIED (253) | no (λ=1 everywhere) | yes: CACC B=2 via CACC, ACC B=2 via CACC | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CACC: 4 conjunct(s); L.ACC: 4 conjunct(s); R.... | no (no widened atom kept) | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `platoon_profiles` | CERTIFIED (220) | yes: SPORT λ=6/5 (affine dynamics) | yes: SPORT B=2 via CACC | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.SPORT: 4 conjunct(s); R.CACC: 4 conjunct(s)) ... | no (no widened atom kept) | no (no linear-form atom kept) | controller-refinement; dim 2; conjunctive |
| `quad_light_lag` | CERTIFIED (169) | yes: CLIMB λ=6/5 (affine dynamics) | yes: CLIMB B=2 via CLIMB | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 4 conjunct(s); R.CLIMB: 3 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `quad_light_profiles` | CERTIFIED (10041) | yes: ECO λ=5/4, NORMAL λ=6/5, SPORT λ=29/25 (affine dynamics) | yes: ECO B=2 via ECO +choice NORMAL:hop/SPORT:hop, NORMAL B=2 via N... | yes: ECO branch=2, NORMAL branch=2, SPORT branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.ECO: 3 conjunct(s); L.NORMAL: 3 conjunct(s); ... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 2; conjunctive |
| `rampmeter_poll_2to1` | CERTIFIED (2195) | no (λ=1 everywhere) | yes: R1800 B=2 via R1200/R1440/R1800, R1440 B=2 via R1200/R1440/R18... | yes: R1800 branch=2, R1440 branch=2, R1200 branch=2, R960 branch=2,... | vacuous: pruned R1440->R1800 but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.R1800: 3 conjunct(s); L.R1440: 5 conjunct(s);... | vacuous: widened atoms kept (L.R720: k <= 39 kind=closure entry=wea... | no (no linear-form atom kept) | degraded-network; dim 3; conjunctive |
| `reactor_feed_wireless` | CERTIFIED (745) | no (λ=1 everywhere) | yes: F1 B=2 via F1/F2, F2 B=2 via F1/F2/F3, F3 B=2 via F2/F3/F4, F4... | yes: F1 branch=2, F2 branch=2, F3 branch=2, F4 branch=2 | yes: pruned F1->F4, F2->F4, F3->F1, F4->F1; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.F1: 4 conjunct(s); L.F2: 4 conjunct(s); L.F3:... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 2; conjunctive |
| `rover_ladder_2to3` | CERTIFIED (329) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `rover_ladder_3to6` | CERTIFIED (729) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_ladder_6to8` | CERTIFIED (15026) | yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; quadratic+conj |
| `rover_ladder_8to12` | CERTIFIED (31424) | yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic+conj |
| `rover_patrol_lag` | CERTIFIED (1279) | yes: FAST λ=11/8 (affine dynamics) | yes: FAST B=2 via FAST/MEDIUM_BRISK +RO | yes: FAST branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.SLOW: 1 conjunct(s); L.MEDIUM_ECO: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `rover_terrain_2to4` | CERTIFIED (588) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 4; conjunctive |
| `rover_terrain_4to6` | CERTIFIED (1103) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_terrain_6to12` | CERTIFIED (1792) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 3 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `sat3w_detumble_phases` | CERTIFIED (20261) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE ... | no (max non-self successors at a joint step = 1) | vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 6; quadratic |
| `sat_detumble_phases` | CERTIFIED (7135) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE ... | no (max non-self successors at a joint step = 1) | vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 4; quadratic |
| `sat_detumble_weak` | CERTIFIED (4068) | yes: DETUMBLE λ=4/5 (polynomial dynamics) | yes: DETUMBLE B=2 via NOMINAL +choice ECONOMY:hop/SURVIVAL:hop | yes: DETUMBLE branch=2 | vacuous: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE but NO... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunc... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | degraded-actuator; dim 4; quadratic |
| `syringe_relay_prearm` | CERTIFIED (1104) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 13/13 handoffs unsat, rows differ | vacuous: cuts kept (L.RUN1: 8 conjunct(s); L.PREARM: 8 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | controller-change; dim 4; conjunctive |
| `tank_dos_3to1` | CERTIFIED (878) | no (λ=1 everywhere) | yes: P2 B=3 via P2/P3, P3 B=3 via P3/P4, P4 B=3 via P4/P5, P5 B=3 v... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.P2: 4 conjunct(s); L.P3: 3 conjunct(s); L.P4: 3 conjunct(s);... | vacuous: widened atoms kept (L.P2: w <= 22.0 kind=implied-contracti... | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `train_ato_odometry` | CERTIFIED (2194) | yes: PL1 λ=6/5 (per pairing: {'PL1': '39/40', 'PL2': '43/40'}), PL2... | yes: PL1 B=2 via PL1/PL2/PL3, PL2 B=2 via PL1/PL2/PL3 | yes: PL1 branch=2, PL2 branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.PL1: 2 conjunct(s); L.PL2: 2 conjunct(s); L.P... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 1; conjunctive |
| `turbine_startup_gearratio` | CERTIFIED (474) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | yes: pruned SPINUP->STOP, RAMP->STOP; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.SPINUP: 2 conjunct(s); L.RAMP: 2 conjunct(s); L.GEN: 1 conju... | yes: L.SPINUP: w <= 9 kind=implied-contraction entry=rational route... | no (no linear-form atom kept) | degraded-controller (configuration error after a gearbox exchange); dim 1; conjunctive |
| `ventilator_vc_cuffleak` | CERTIFIED (253) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | yes: L.INSP: 1 conjunct(s); L.EXP: 3 conjunct(s); R.INSP: 1 conjunc... | yes: L.EXP: s <= 0.01 kind=closure entry=weakening route=frozen; R.... | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `watertank` | CERTIFIED (2079) | yes: Low λ=2, Mid λ=2 (affine dynamics) | yes: Low B=2 via Low/MidBoost/MidEco, Mid B=2 via High/MidBoost/Mid... | yes: Low branch=2, Mid branch=2 | vacuous: pruned Low->PumpOff but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.H... | vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contract... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `watertank_twospeed` | CERTIFIED (1864) | yes: Low λ=2 (per pairing: {'Fast': '1', 'MidEco': '3/2', 'MidBoost... | yes: Low B=2 via Fast/MidBoost/MidEco/Slow, Mid B=2 via High/MidBoo... | yes: Low branch=3, Mid branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.H... | vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contract... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |

## Totals

| mechanism | benchmarks (non-vacuous) | count |
|---|---|---|
| M1 | `acc_spoof_lag`, `acc_tune_lag`, `acc_tune_limp`, `bottling_fill_strainer`, `flaps_slow_approach`, `furnace_program_timebase`, `gantry_speed_zones`, `lit_csf25_salt_tank_hold`, `platoon_profiles`, `quad_light_lag`, `quad_light_profiles`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_patrol_lag`, `sat_detumble_weak`, `train_ato_odometry`, `watertank`, `watertank_twospeed` | 18 |
| M2 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `fuelcell_chp_dos`, `gantry_speed_zones`, `platoon_linkloss`, `platoon_profiles`, `quad_light_lag`, `quad_light_profiles`, `rampmeter_poll_2to1`, `reactor_feed_wireless`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_patrol_lag`, `sat3w_detumble_phases`, `sat_detumble_phases`, `sat_detumble_weak`, `tank_dos_3to1`, `train_ato_odometry`, `watertank`, `watertank_twospeed` | 22 |
| M3 | `acc_spoof_limp`, `fuelcell_chp_dos`, `quad_light_profiles`, `rampmeter_poll_2to1`, `reactor_feed_wireless`, `rover_patrol_lag`, `sat_detumble_weak`, `train_ato_odometry`, `watertank`, `watertank_twospeed` | 10 |
| M4 | `fuelcell_chp_dos`, `reactor_feed_wireless`, `turbine_startup_gearratio` | 3 |
| M5 | `acc_tune_limp`, `antenna_track_kvretune`, `elevator_start_discbrake`, `engine_start_highidle`, `h2_refuel_ambientbias`, `hydro_rejection_gatecal`, `lit_csf25_salt_tank_hold`, `molding_pack_checkring`, `syringe_relay_prearm`, `ventilator_vc_cuffleak` | 10 |
| M6 | `acc_spoof_limp`, `acc_tune_limp`, `bottling_fill_strainer`, `engine_start_highidle`, `fuelcell_chp_dos`, `furnace_program_timebase`, `h2_refuel_ambientbias`, `lit_csf25_salt_tank_hold`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_terrain_2to4`, `rover_terrain_4to6`, `rover_terrain_6to12`, `sat3w_detumble_phases`, `sat_detumble_phases`, `tank_dos_3to1`, `turbine_startup_gearratio`, `ventilator_vc_cuffleak` | 18 |
| M6+ | `engine_start_highidle`, `furnace_program_timebase`, `h2_refuel_ambientbias`, `lit_csf25_salt_tank_hold`, `turbine_startup_gearratio`, `ventilator_vc_cuffleak` | 6 |
| M6L |  | 0 |
| per-mode domains |  | 0 |

## Proposed Table-1 grouping

| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; widened cuts; linear-form chains; per-mode domains) |
|---|---|---|---|---|---|
| ACC under sensor spoofing / retune | 4 | 1, 2 | conjunctive, conjunctive+linear | affine | modes 1-2 / 1-4; 0 with a pruned fallback; 1 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Quadrotor climb, lighter airframe | 2 | 2, 3 | conjunctive | affine | modes 1-3 / 1-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Platoon follower (CACC: link loss, latency, profiles) | 3 | 2, 3 | conjunctive | affine | modes 1-2 / 1-1; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rover patrol (zones) | 1 | 3 | conjunctive | affine | modes 4-4 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Gantry speed zones (multi-cycle matching) | 1 | 2 | conjunctive | affine | modes 3-3 / 1-1; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rover ladder | 4 | 3, 6, 8, 12 | conjunctive, quadratic+conj | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Terrain chain | 3 | 4, 6, 12 | conjunctive | affine + polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 3 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Watertank | 2 | 1 | conjunctive | affine | modes 3-3 / 5-6; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Tank under sampling DoS | 1 | 2 | conjunctive | polynomial | modes 4-4 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Turbofan ground start | 1 | 3 | conjunctive+linear | affine | modes 6-6 / 6-6; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Train speed control (ATO) | 1 | 1 | conjunctive | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Wind turbine start-up | 1 | 1 | conjunctive | affine | modes 4-4 / 4-4; 1 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Injection molding pack and hold | 1 | 3 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Fuel-cell CHP current levels | 1 | 2 | conjunctive | affine | modes 3-3 / 3-3; 1 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Elevator trip | 1 | 3 | conjunctive | affine | modes 4-4 / 4-4; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Heat-treatment furnace program | 1 | 2 | conjunctive | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Syringe-pump relay | 1 | 4 | conjunctive | affine | modes 6-6 / 4-4; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Hydro unit load rejection | 1 | 3 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Volume-controlled ventilation | 1 | 2 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Freeway ramp metering (polled detectors) | 1 | 3 | conjunctive | affine | modes 6-6 / 6-6; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Bottle filler (clogged product strainer) | 1 | 2 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Airliner flap extension (one hydraulic system lost) | 1 | 2 | conjunctive | polynomial | modes 2-2 / 2-2; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Ground-station antenna (servo retune) | 1 | 3 | conjunctive | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rigid-body detumbling (polynomial) | 3 | 4, 6 | quadratic | polynomial | modes 1-2 / 3-4; 0 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Hydrogen refuelling (sensor bias) | 1 | 1 | conjunctive+linear | affine | modes 5-5 / 5-5; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Exothermic reactor feed interlock | 1 | 2 | conjunctive | affine | modes 4-4 / 4-4; 1 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Literature | 9 | 1, 2, 3, 6/2 | conjunctive, quadratic, quadratic+conj | affine | modes 2-48 / 2-12; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| other | 1 | 1 | conjunctive | affine | modes 3-3 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| **total** | **50** | | | | |

## Duplicate check

no two benchmarks normalize to the same model; no two benchmarks differ only in tolerance constants (rows' numerals masked)

## Timing

| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 2/2 | CERTIFIED | 139 | 0.41 | - | - | - | - |
| `acc_spoof_limp` | 1/1 | CERTIFIED | 184 | 0.45 | - | - | - | - |
| `acc_tune_lag` | 2/2 | CERTIFIED | 168 | 0.43 | - | - | - | - |
| `acc_tune_limp` | 1/1 | CERTIFIED | 614 | 0.88 | - | - | - | - |
| `antenna_track_kvretune` | 3/3 | CERTIFIED | 898 | 1.16 | - | - | - | - |
| `bottling_fill_strainer` | 2/2 | CERTIFIED | 571 | 0.83 | - | - | - | - |
| `canal_gate_notches` | 1/1 | CERTIFIED | 317 | 0.58 | - | - | - | - |
| `elevator_start_discbrake` | 3/3 | CERTIFIED | 990 | 1.25 | - | - | - | - |
| `engine_start_highidle` | 3/3 | CERTIFIED | 743 | 1.01 | - | - | - | - |
| `flaps_slow_approach` | 2/2 | CERTIFIED | 303 | 0.57 | - | - | - | - |
| `fuelcell_chp_dos` | 2/2 | CERTIFIED | 463 | 0.72 | - | - | - | - |
| `furnace_program_timebase` | 2/2 | CERTIFIED | 1132 | 1.39 | - | - | - | - |
| `gantry_speed_zones` | 2/2 | CERTIFIED | 1250 | 1.5 | - | - | - | - |
| `h2_refuel_ambientbias` | 1/1 | CERTIFIED | 617 | 0.87 | - | - | - | - |
| `hydro_rejection_gatecal` | 3/3 | CERTIFIED | 312 | 0.5 | - | - | - | - |
| `lit_csf21_vehicle_bus` | 3/3 | CERTIFIED | 3275 | 3.5 | - | - | - | - |
| `lit_csf21_vehicle_thermo` | 3/3 | CERTIFIED | 1756 | 2.0 | - | - | - | - |
| `lit_csf25_salt_tank_hold` | 2/2 | CERTIFIED | 294 | 0.53 | - | - | - | - |
| `lit_drl_lane_control` | 3/3 | CERTIFIED | 2670 | 2.94 | - | - | - | - |
| `lit_freedm_meter` | 2/2 | CERTIFIED | 2292 | 2.55 | - | - | - | - |
| `lit_girard08_robot` | 6/2 | CERTIFIED | 53551 | 53.76 | - | - | - | - |
| `lit_gpt10_boost_converter` | 2/2 | CERTIFIED | 50932 | 51.21 | - | - | - | - |
| `lit_lz21_vehicle_position` | 2/2 | CERTIFIED | 413 | 0.63 | - | - | - | - |
| `lit_nahs25_salt_tank` | 1/1 | CERTIFIED | 197 | 0.47 | - | - | - | - |
| `molding_pack_checkring` | 3/3 | CERTIFIED | 398 | 0.67 | - | - | - | - |
| `platoon_latency` | 3/3 | CERTIFIED | 395 | 0.66 | - | - | - | - |
| `platoon_linkloss` | 2/2 | CERTIFIED | 253 | 0.53 | - | - | - | - |
| `platoon_profiles` | 2/2 | CERTIFIED | 220 | 0.46 | - | - | - | - |
| `quad_light_lag` | 3/3 | CERTIFIED | 169 | 0.43 | - | - | - | - |
| `quad_light_profiles` | 2/2 | CERTIFIED | 10041 | 10.31 | - | - | - | - |
| `rampmeter_poll_2to1` | 3/3 | CERTIFIED | 2195 | 2.47 | - | - | - | - |
| `reactor_feed_wireless` | 2/2 | CERTIFIED | 745 | 1.01 | - | - | - | - |
| `rover_ladder_2to3` | 3/3 | CERTIFIED | 329 | 0.59 | - | - | - | - |
| `rover_ladder_3to6` | 6/6 | CERTIFIED | 729 | 0.98 | - | - | - | - |
| `rover_ladder_6to8` | 8/8 | CERTIFIED | 15026 | 15.3 | - | - | - | - |
| `rover_ladder_8to12` | 12/12 | CERTIFIED | 31424 | 31.63 | - | - | - | - |
| `rover_patrol_lag` | 3/3 | CERTIFIED | 1279 | 1.54 | - | - | - | - |
| `rover_terrain_2to4` | 4/4 | CERTIFIED | 588 | 0.85 | - | - | - | - |
| `rover_terrain_4to6` | 6/6 | CERTIFIED | 1103 | 1.37 | - | - | - | - |
| `rover_terrain_6to12` | 12/12 | CERTIFIED | 1792 | 2.06 | - | - | - | - |
| `sat3w_detumble_phases` | 6/6 | CERTIFIED | 20261 | 20.5 | - | - | - | - |
| `sat_detumble_phases` | 4/4 | CERTIFIED | 7135 | 7.41 | - | - | - | - |
| `sat_detumble_weak` | 4/4 | CERTIFIED | 4068 | 4.32 | - | - | - | - |
| `syringe_relay_prearm` | 4/4 | CERTIFIED | 1104 | 1.37 | - | - | - | - |
| `tank_dos_3to1` | 2/2 | CERTIFIED | 878 | 1.02 | - | - | - | - |
| `train_ato_odometry` | 1/1 | CERTIFIED | 2194 | 2.46 | - | - | - | - |
| `turbine_startup_gearratio` | 1/1 | CERTIFIED | 474 | 0.73 | - | - | - | - |
| `ventilator_vc_cuffleak` | 2/2 | CERTIFIED | 253 | 0.51 | - | - | - | - |
| `watertank` | 1/1 | CERTIFIED | 2079 | 2.3 | - | - | - | - |
| `watertank_twospeed` | 1/1 | CERTIFIED | 1864 | 2.14 | - | - | - | - |
| **total** | | | **231077** | | | **0** | | |

## Per-benchmark run records

### `acc_spoof_lag`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 2/2; modes L/R 1/1; εL/εR 0.1/0.1; λ ∈ [1.5, 1.5]; invariant shape conjunctive; rows identical: True; normalized md5 `e49a92cb5bb5`
* `relcert`: **CERTIFIED** (139 ms); `[prune] acc_spoof_lag: []`; NO_PRUNE: **CERTIFIED** (124 ms); NO_CUT: **CERTIFIED** (94 ms); NO_IMPLIED_CUT: **CERTIFIED** (153 ms); NO_LINEAR_CUT: **CERTIFIED** (101 ms); domains: uniform
* `[cut] L.CRUISE: 4 conjunct(s)`
* `[cut] R.CRUISE: 4 conjunct(s)`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (73 ms)
* cover `CRUISE_L`: λ = 3/2, budget 2, admissible ['CRUISE'], flags {'CRUISE': 'j--'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=2 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `acc_spoof_limp`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0acc968c2ceb`
* `relcert`: **CERTIFIED** (184 ms); `[prune] acc_spoof_limp: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (179 ms); NO_CUT: **DECLINED** (270 ms); NO_IMPLIED_CUT: **CERTIFIED** (238 ms); NO_LINEAR_CUT: **CERTIFIED** (268 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.ECO: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, ECO, SPORT]`
* `[admissible] LIMP_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (96 ms)
* cover `CRUISE_L`: λ = 1, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1)`
    * from `ECO`: `ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1)`
    * from `ECO`: `ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: CRUISE B=2 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT; **M3** yes: CRUISE branch=2, LIMP branch=2; **M4** vacuous: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `acc_tune_lag`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 2/2; modes L/R 1/1; εL/εR 0.1/0.1; λ ∈ [2.0, 2.0]; invariant shape conjunctive; rows identical: True; normalized md5 `e84e7547519d`
* `relcert`: **CERTIFIED** (168 ms); `[prune] acc_tune_lag: []`; NO_PRUNE: **CERTIFIED** (162 ms); NO_CUT: **CERTIFIED** (137 ms); NO_IMPLIED_CUT: **CERTIFIED** (89 ms); NO_LINEAR_CUT: **CERTIFIED** (85 ms); domains: uniform
* `[cut] L.CRUISE: 4 conjunct(s)`
* `[cut] R.CRUISE: 4 conjunct(s)`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (94 ms)
* cover `CRUISE_L`: λ = 2, budget 2, admissible ['CRUISE'], flags {'CRUISE': 'j--'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=2 (affine dynamics); **M2** yes: CRUISE B=2 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `acc_tune_limp`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [1.0, 1.5]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `7cda9de8aa3f`
* `relcert`: **CERTIFIED** (614 ms); `[prune] acc_tune_limp: [NORMAL->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (614 ms); NO_CUT: **DECLINED** (720 ms); NO_IMPLIED_CUT: **CERTIFIED** (490 ms); NO_LINEAR_CUT: **CERTIFIED** (628 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL]`
* `[admissible] LIMP_L: [NORMAL]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (102 ms)
* cover `CRUISE_L`: λ = 3/2, budget 2, admissible ['NORMAL'], flags {'NORMAL': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['NORMAL'], branching 0, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1]; NORMAL:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 1, admissible ['NORMAL'], flags {'NORMAL': 'j--', 'DISENGAGE': '---'}, kinds ['base'], path modes ['NORMAL'], branching 0, right-only False
    * from `NORMAL`: `NORMAL:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=2 via NORMAL; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned NORMAL->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `antenna_track_kvretune`

* family: Ground-station antenna (servo retune); scenario: controller-change; dims L/R 3/3; modes L/R 3/3; εL/εR 0.05/0.05; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `4d52fbfcc283`
* `relcert`: **CERTIFIED** (898 ms); `[prune] antenna_track_kvretune: []`; NO_PRUNE: **CERTIFIED** (1871 ms); NO_CUT: **CERTIFIED** (897 ms); NO_IMPLIED_CUT: **CERTIFIED** (902 ms); NO_LINEAR_CUT: **CERTIFIED** (908 ms); domains: uniform
* `[cut] L.TRACK: 4 conjunct(s)`
* `[cut] L.STOW: 3 conjunct(s)`
* `[cut] L.STOWED: 5 conjunct(s)`
* `[cut] R.TRACK: 4 conjunct(s)`
* `[cut] R.STOW: 3 conjunct(s)`
* `[cut] R.STOWED: 5 conjunct(s)`
* `[admissible] TRACK_L: [TRACK]`
* `[admissible] STOW_L: [STOW]`
* `[admissible] STOWED_L: [STOWED]`
* `--handoff`: 6/6 checked, 6 passed, failing -, non-vacuous (105 ms)
* cover `TRACK_L`: λ = 1, budget 1, admissible ['TRACK'], flags {'TRACK': 'j--', 'STOW': '---', 'STOWED': 'j--'}, kinds ['base'], path modes ['TRACK'], branching 0, right-only False
    * from `TRACK`: `TRACK:base(B=1)`
* cover `STOW_L`: λ = 1, budget 1, admissible ['STOW'], flags {'TRACK': '---', 'STOW': 'j--', 'STOWED': '---'}, kinds ['base'], path modes ['STOW'], branching 0, right-only False
    * from `STOW`: `STOW:base(B=1)`
* cover `STOWED_L`: λ = 1, budget 1, admissible ['STOWED'], flags {'TRACK': 'j--', 'STOW': '---', 'STOWED': 'j--'}, kinds ['base'], path modes ['STOWED'], branching 0, right-only False
    * from `STOWED`: `STOWED:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 6/6 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.TRACK: 4 conjunct(s); L.STOW: 3 conjunct(s); L.STOWED: 5 conjunct(s); R.TRACK: 4 conjunct(s); R.STOW: 3 conjunct(s); R.STOWED: 5 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `bottling_fill_strainer`

* family: Bottle filler (clogged product strainer); scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.005/0.005; λ ∈ [0.8, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `6216c5a1124b`
* `relcert`: **CERTIFIED** (571 ms); `[prune] bottling_fill_strainer: []`; NO_PRUNE: **CERTIFIED** (578 ms); NO_CUT: **DECLINED** (1327 ms); NO_IMPLIED_CUT: **CERTIFIED** (569 ms); NO_LINEAR_CUT: **CERTIFIED** (554 ms); domains: uniform
* `[cut] L.FILL: 4 conjunct(s)`
* `[cut] L.CLOSE: 4 conjunct(s)`
* `[cut] R.FILL: 4 conjunct(s)`
* `[cut] R.CLOSE: 4 conjunct(s)`
* `[admissible] FILL_L: [FILL]`
* `[admissible] CLOSE_L: [CLOSE]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (89 ms)
* cover `FILL_L`: λ = 17/20, budget 1, admissible ['FILL'], flags {'FILL': 'j--', 'CLOSE': '---'}, kinds ['base'], path modes ['FILL'], branching 0, right-only False
    * from `FILL`: `FILL:base(B=1)`
* cover `CLOSE_L`: λ = 1, budget 1, admissible ['CLOSE'], flags {'FILL': '---', 'CLOSE': 'j--'}, kinds ['base'], path modes ['CLOSE'], branching 0, right-only False
    * from `CLOSE`: `CLOSE:base(B=1)`
* cells: **M1** yes: FILL λ=17/20 (affine dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.FILL: 4 conjunct(s); L.CLOSE: 4 conjunct(s); R.FILL: 4 conjunct(s); R.CLOSE: 4 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `canal_gate_notches`

* family: other; scenario: controller-refinement; dims L/R 1/1; modes L/R 3/4; εL/εR 10.0/10.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `aa73d8924ee1`
* `relcert`: **CERTIFIED** (317 ms); `[prune] canal_gate_notches: []`; NO_PRUNE: **CERTIFIED** (385 ms); NO_CUT: **CERTIFIED** (277 ms); NO_IMPLIED_CUT: **CERTIFIED** (344 ms); NO_LINEAR_CUT: **CERTIFIED** (368 ms); domains: uniform
* `[cut] L.RAISE: 2 conjunct(s)`
* `[cut] L.HOLD: 2 conjunct(s)`
* `[cut] L.LOWER: 2 conjunct(s)`
* `[cut] R.N100: 2 conjunct(s)`
* `[cut] R.N75: 2 conjunct(s)`
* `[cut] R.N50: 2 conjunct(s)`
* `[cut] R.N25: 2 conjunct(s)`
* `[cut-x] L.RAISE: h <= 0.95 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.HOLD: h <= 0.9 kind=closure entry=weakening route=shape`
* `[cut-x] L.LOWER: h >= 0.3 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.N100: h <= 1 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.N25: h >= 0.25 kind=implied-contraction entry=rational route=shape`
* `[admissible] RAISE_L: [N100, N75, N50]`
* `[admissible] HOLD_L: [N100, N75, N50, N25]`
* `[admissible] LOWER_L: [N75, N50, N25]`
* `--handoff`: 7/7 checked, 7 passed, failing -, VACUOUS (identical rows) (85 ms)
* cover `RAISE_L`: λ = 1, budget 1, admissible ['N100', 'N75', 'N50'], flags {'N100': 'j--', 'N75': '---', 'N50': '---', 'N25': '---'}, kinds ['base', 'hop'], path modes ['N100', 'N50', 'N75'], branching 0, right-only False
    * from `N100`: `N100:base(B=1)`
    * from `N75`: `N75:hop(B=1,preJ)->[N100@1]; N100:base(B=1)`
    * from `N50`: `N50:hop(B=1,preJ)->[N100@1]; N100:base(B=1)`
* cover `HOLD_L`: λ = 1, budget 1, admissible ['N100', 'N75', 'N50', 'N25'], flags {'N100': '---', 'N75': 'j--', 'N50': 'j--', 'N25': '---'}, kinds ['base', 'hop'], path modes ['N100', 'N25', 'N50', 'N75'], branching 0, right-only False
    * from `N100`: `N100:hop(B=1,preJ)->[N75@1, N50@1]; N75:base(B=1); N50:base(B=1)`
    * from `N75`: `N75:base(B=1)`
    * from `N50`: `N50:base(B=1)`
    * from `N25`: `N25:hop(B=1,preJ)->[N75@1, N50@1]; N75:base(B=1); N50:base(B=1)`
* cover `LOWER_L`: λ = 1, budget 1, admissible ['N75', 'N50', 'N25'], flags {'N100': '---', 'N75': '---', 'N50': '---', 'N25': 'j--'}, kinds ['base', 'hop'], path modes ['N25', 'N50', 'N75'], branching 0, right-only False
    * from `N75`: `N75:hop(B=1,preJ)->[N25@1]; N25:base(B=1)`
    * from `N50`: `N50:hop(B=1,preJ)->[N25@1]; N25:base(B=1)`
    * from `N25`: `N25:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.RAISE: 2 conjunct(s); L.HOLD: 2 conjunct(s); L.LOWER: 2 conjunct(s); R.N100: 2 conjunct(s); R.N75: 2 conjunct(s); R.N50: 2 conjunct(s); R.N25: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.RAISE: h <= 0.95 kind=implied-contraction entry=rational route=shape; L.HOLD: h <= 0.9 kind=closure entry=weakening route=shape; L.LOWER: h >= 0.3 kind=implied-contraction entry=rational route=shape; R.N100: h <= 1 kind=implied-contraction entry=rational route=shape; R.N25: h >= 0.25 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `elevator_start_discbrake`

* family: Elevator trip; scenario: actuator-change; dims L/R 3/3; modes L/R 4/4; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `18047bc26501`
* `relcert`: **CERTIFIED** (990 ms); `[prune] elevator_start_discbrake: []`; NO_PRUNE: **CERTIFIED** (900 ms); NO_CUT: **CERTIFIED** (891 ms); NO_IMPLIED_CUT: **CERTIFIED** (875 ms); NO_LINEAR_CUT: **CERTIFIED** (981 ms); domains: uniform
* `[cut] L.LIFT: 8 conjunct(s)`
* `[cut] L.UP: 6 conjunct(s)`
* `[cut] L.APP: 6 conjunct(s)`
* `[cut] L.STOP: 5 conjunct(s)`
* `[cut] R.LIFT: 8 conjunct(s)`
* `[cut] R.UP: 6 conjunct(s)`
* `[cut] R.APP: 6 conjunct(s)`
* `[cut] R.STOP: 5 conjunct(s)`
* `[admissible] LIFT_L: [LIFT]`
* `[admissible] UP_L: [LIFT, UP]`
* `[admissible] APP_L: [APP]`
* `[admissible] STOP_L: [STOP]`
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (98 ms)
* cover `LIFT_L`: λ = 1, budget 1, admissible ['LIFT'], flags {'LIFT': 'j--', 'UP': '---', 'APP': 'j--', 'STOP': 'j--'}, kinds ['base'], path modes ['LIFT'], branching 0, right-only False
    * from `LIFT`: `LIFT:base(B=1)`
* cover `UP_L`: λ = 1, budget 1, admissible ['LIFT', 'UP'], flags {'LIFT': '-dd', 'UP': 'j--', 'APP': '---', 'STOP': '---'}, kinds ['base', 'repoDyn'], path modes ['LIFT', 'UP'], branching 0, right-only True
    * from `LIFT`: `LIFT:repoDyn(B=1,preJ)->[UP@1]; UP:base(B=1)`
    * from `UP`: `UP:base(B=1)`
* cover `APP_L`: λ = 1, budget 1, admissible ['APP'], flags {'LIFT': 'jdd', 'UP': '---', 'APP': 'j--', 'STOP': '---'}, kinds ['base'], path modes ['APP'], branching 0, right-only False
    * from `APP`: `APP:base(B=1)`
* cover `STOP_L`: λ = 1, budget 1, admissible ['STOP'], flags {'LIFT': 'jdd', 'UP': '---', 'APP': '---', 'STOP': 'j--'}, kinds ['base'], path modes ['STOP'], branching 0, right-only False
    * from `STOP`: `STOP:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 7/7 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.LIFT: 8 conjunct(s); L.UP: 6 conjunct(s); L.APP: 6 conjunct(s); L.STOP: 5 conjunct(s); R.LIFT: 8 conjunct(s); R.UP: 6 conjunct(s); R.APP: 6 conjunct(s); R.STOP: 5 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `engine_start_highidle`

* family: Turbofan ground start; scenario: controller-change; dims L/R 3/3; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `634381c4084e`
* `relcert`: **CERTIFIED** (743 ms); `[prune] engine_start_highidle: []`; NO_PRUNE: **CERTIFIED** (750 ms); NO_CUT: **DECLINED** (250 ms); NO_IMPLIED_CUT: **DECLINED** (245 ms); NO_LINEAR_CUT: **CERTIFIED** (787 ms); domains: uniform
* `[cut] L.STARTER: 3 conjunct(s)`
* `[cut] L.STARTER_LOW: 3 conjunct(s)`
* `[cut] L.LIGHTOFF: 2 conjunct(s)`
* `[cut] L.SELF: 2 conjunct(s)`
* `[cut] L.IDLE: 1 conjunct(s)`
* `[cut] L.ABORT: 2 conjunct(s)`
* `[cut] R.STARTER: 3 conjunct(s)`
* `[cut] R.STARTER_LOW: 3 conjunct(s)`
* `[cut] R.LIGHTOFF: 2 conjunct(s)`
* `[cut] R.SELF: 2 conjunct(s)`
* `[cut] R.IDLE: 1 conjunct(s)`
* `[cut] R.ABORT: 2 conjunct(s)`
* `[cut-x] L.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STARTER_LOW: p <= 35.0 kind=closure entry=weakening route=frozen`
* `[cut-x] L.STARTER_LOW: n <= 25.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.SELF: n <= 66 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABORT: n <= 25.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STARTER_LOW: p <= 35.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.STARTER_LOW: n <= 25.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.SELF: n <= 62 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABORT: n <= 25.0 kind=closure entry=weakening route=frozen`
* `[admissible] STARTER_L: [STARTER, LIGHTOFF, SELF, IDLE]`
* `[admissible] STARTER_LOW_L: [STARTER_LOW, LIGHTOFF, SELF, IDLE]`
* `[admissible] LIGHTOFF_L: [LIGHTOFF, SELF, IDLE]`
* `[admissible] SELF_L: [LIGHTOFF, SELF, IDLE]`
* `[admissible] IDLE_L: [SELF, IDLE]`
* `[admissible] ABORT_L: [STARTER, STARTER_LOW, LIGHTOFF, SELF, IDLE, ABORT]`
* `--handoff`: 12/12 checked, 12 passed, failing -, non-vacuous (113 ms)
* cover `STARTER_L`: λ = 1, budget 1, admissible ['STARTER', 'LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': 'j--', 'STARTER_LOW': '---', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': '---'}, kinds ['base'], path modes ['IDLE', 'LIGHTOFF', 'SELF', 'STARTER'], branching 0, right-only False
    * from `STARTER`: `STARTER:base(B=1)`
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `STARTER_LOW_L`: λ = 1, budget 1, admissible ['STARTER_LOW', 'LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': 'jd-', 'STARTER_LOW': 'j--', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': '---'}, kinds ['base'], path modes ['IDLE', 'LIGHTOFF', 'SELF', 'STARTER_LOW'], branching 0, right-only False
    * from `STARTER_LOW`: `STARTER_LOW:base(B=1)`
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `LIGHTOFF_L`: λ = 1, budget 1, admissible ['LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': '-dd', 'STARTER_LOW': '-dd', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': '---'}, kinds ['base'], path modes ['IDLE', 'LIGHTOFF', 'SELF'], branching 0, right-only False
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `SELF_L`: λ = 1, budget 1, admissible ['LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': 'jdd', 'STARTER_LOW': 'jdd', 'LIGHTOFF': '-dd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base', 'repoDyn'], path modes ['IDLE', 'LIGHTOFF', 'SELF'], branching 0, right-only True
    * from `LIGHTOFF`: `LIGHTOFF:repoDyn(B=1,preJ)->[SELF@1]; SELF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `IDLE_L`: λ = 1, budget 1, admissible ['SELF', 'IDLE'], flags {'STARTER': 'jdd', 'STARTER_LOW': 'jdd', 'LIGHTOFF': 'jdd', 'SELF': '-dd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base', 'repoDyn'], path modes ['IDLE', 'SELF'], branching 0, right-only True
    * from `SELF`: `SELF:repoDyn(B=1,preJ)->[IDLE@1]; IDLE:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `ABORT_L`: λ = 1, budget 1, admissible ['STARTER', 'STARTER_LOW', 'LIGHTOFF', 'SELF', 'IDLE', 'ABORT'], flags {'STARTER': 'jdd', 'STARTER_LOW': 'jdd', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['ABORT', 'IDLE', 'LIGHTOFF', 'SELF', 'STARTER', 'STARTER_LOW'], branching 0, right-only False
    * from `STARTER`: `STARTER:base(B=1)`
    * from `STARTER_LOW`: `STARTER_LOW:base(B=1)`
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
    * from `ABORT`: `ABORT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 12/12 handoffs unsat, rows differ; **M6** yes: L.STARTER: 3 conjunct(s); L.STARTER_LOW: 3 conjunct(s); L.LIGHTOFF: 2 conjunct(s); L.SELF: 2 conjunct(s); L.IDLE: 1 conjunct(s); L.ABORT: 2 conjunct(s); R.STARTER: 3 conjunct(s); R.STARTER_LOW: 3 conjunct(s); R.LIGHTOFF: 2 conjunct(s); R.SELF: 2 conjunct(s); R.IDLE: 1 conjunct(s); R.ABORT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape; L.STARTER_LOW: p <= 35.0 kind=closure entry=weakening route=frozen; L.STARTER_LOW: n <= 25.5 kind=implied-contraction entry=rational route=shape; L.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape; L.SELF: n <= 66 kind=implied-contraction entry=rational route=shape; L.ABORT: n <= 25.0 kind=closure entry=weakening route=frozen; R.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape; R.STARTER_LOW: p <= 35.0 kind=closure entry=weakening route=frozen; R.STARTER_LOW: n <= 25.5 kind=implied-contraction entry=rational route=shape; R.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape; R.SELF: n <= 62 kind=implied-contraction entry=rational route=shape; R.ABORT: n <= 25.0 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `flaps_slow_approach`

* family: Airliner flap extension (one hydraulic system lost); scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [0.5, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `c0942e772ec0`
* `relcert`: **CERTIFIED** (303 ms); `[prune] flaps_slow_approach: []`; NO_PRUNE: **CERTIFIED** (326 ms); NO_CUT: **CERTIFIED** (246 ms); NO_IMPLIED_CUT: **CERTIFIED** (238 ms); NO_LINEAR_CUT: **CERTIFIED** (319 ms); domains: uniform
* `[cut] L.EXT: 3 conjunct(s)`
* `[cut] L.CONF2: 5 conjunct(s)`
* `[cut] R.EXT: 3 conjunct(s)`
* `[cut] R.CONF2: 5 conjunct(s)`
* `[admissible] EXT_L: [EXT]`
* `[admissible] CONF2_L: [CONF2]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `EXT_L`: λ = 1/2, budget 1, admissible ['EXT'], flags {'EXT': 'j--', 'CONF2': '---'}, kinds ['base'], path modes ['EXT'], branching 0, right-only False
    * from `EXT`: `EXT:base(B=1)`
* cover `CONF2_L`: λ = 1, budget 1, admissible ['CONF2'], flags {'EXT': '---', 'CONF2': 'j--'}, kinds ['base'], path modes ['CONF2'], branching 0, right-only False
    * from `CONF2`: `CONF2:base(B=1)`
* cells: **M1** yes: EXT λ=1/2 (polynomial dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.EXT: 3 conjunct(s); L.CONF2: 5 conjunct(s); R.EXT: 3 conjunct(s); R.CONF2: 5 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `fuelcell_chp_dos`

* family: Fuel-cell CHP current levels; scenario: dos-attack; dims L/R 2/2; modes L/R 3/3; εL/εR 20.0/10.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `d86d2e057007`
* `relcert`: **CERTIFIED** (463 ms); `[prune] fuelcell_chp_dos: [LOW->HIGH, HIGH->LOW]`; NO_PRUNE: **DECLINED** (234 ms); NO_CUT: **DECLINED** (255 ms); NO_IMPLIED_CUT: **CERTIFIED** (510 ms); NO_LINEAR_CUT: **CERTIFIED** (530 ms); domains: uniform
* `[cut] L.LOW: 5 conjunct(s)`
* `[cut] L.MED: 5 conjunct(s)`
* `[cut] L.HIGH: 5 conjunct(s)`
* `[cut] R.LOW: 5 conjunct(s)`
* `[cut] R.MED: 5 conjunct(s)`
* `[cut] R.HIGH: 5 conjunct(s)`
* `[admissible] LOW_L: [LOW, MED]`
* `[admissible] MED_L: [LOW, MED, HIGH]`
* `[admissible] HIGH_L: [MED, HIGH]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (68 ms)
* cover `LOW_L`: λ = 1, budget 2, admissible ['LOW', 'MED'], flags {'LOW': 'j--', 'MED': 'j--', 'HIGH': '---'}, kinds ['base', 'hop', 'joint'], path modes ['LOW', 'MED'], branching 1, right-only False
    * from `LOW`: `LOW:joint(B=2)->[LOW@1, LOW@1, MED@1]; LOW:base(B=1); MED:base(B=1)`
    * from `MED`: `MED:hop(B=2,preJ)->[LOW@2]; LOW:joint(B=2)->[LOW@1, LOW@1, MED@1]; LOW:base(B=1); MED:base(B=1)`
* cover `MED_L`: λ = 1, budget 2, admissible ['LOW', 'MED', 'HIGH'], flags {'LOW': 'j--', 'MED': 'j--', 'HIGH': 'j--'}, kinds ['base', 'joint'], path modes ['HIGH', 'LOW', 'MED'], branching 2, right-only False
    * from `LOW`: `LOW:joint(B=2)->[LOW@1, LOW@1, MED@1]; LOW:base(B=1); MED:base(B=1)`
    * from `MED`: `MED:joint(B=2)->[MED@1, LOW@1, MED@1, HIGH@1]; MED:base(B=1); LOW:base(B=1); HIGH:base(B=1)`
    * from `HIGH`: `HIGH:joint(B=2)->[HIGH@1, MED@1, HIGH@1]; HIGH:base(B=1); MED:base(B=1)`
* cover `HIGH_L`: λ = 1, budget 2, admissible ['MED', 'HIGH'], flags {'LOW': '---', 'MED': 'j--', 'HIGH': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['HIGH', 'MED'], branching 1, right-only False
    * from `MED`: `MED:hop(B=2,preJ)->[HIGH@2]; HIGH:joint(B=2)->[HIGH@1, MED@1, HIGH@1]; HIGH:base(B=1); MED:base(B=1)`
    * from `HIGH`: `HIGH:joint(B=2)->[HIGH@1, MED@1, HIGH@1]; HIGH:base(B=1); MED:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: LOW B=2 via LOW +choice MED:hop, MED B=2 via HIGH/LOW/MED, HIGH B=2 via HIGH +choice MED:hop; **M3** yes: MED branch=2; **M4** yes: pruned LOW->HIGH, HIGH->LOW; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.LOW: 5 conjunct(s); L.MED: 5 conjunct(s); L.HIGH: 5 conjunct(s); R.LOW: 5 conjunct(s); R.MED: 5 conjunct(s); R.HIGH: 5 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `furnace_program_timebase`

* family: Heat-treatment furnace program; scenario: controller-change; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [0.8, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `854fb41fd15a`
* `relcert`: **CERTIFIED** (1132 ms); `[prune] furnace_program_timebase: []`; NO_PRUNE: **CERTIFIED** (1101 ms); NO_CUT: **DECLINED** (3045 ms); NO_IMPLIED_CUT: **DECLINED** (3731 ms); NO_LINEAR_CUT: **CERTIFIED** (1133 ms); domains: uniform
* `[cut] L.PREHEAT: 3 conjunct(s)`
* `[cut] L.HEAT: 4 conjunct(s)`
* `[cut] L.SOAK: 4 conjunct(s)`
* `[cut] R.PREHEAT: 3 conjunct(s)`
* `[cut] R.HEAT: 4 conjunct(s)`
* `[cut] R.SOAK: 4 conjunct(s)`
* `[cut-x] L.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] PREHEAT_L: [PREHEAT]`
* `[admissible] HEAT_L: [HEAT]`
* `[admissible] SOAK_L: [SOAK]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (96 ms)
* cover `PREHEAT_L`: λ = 4/5, budget 1, admissible ['PREHEAT'], flags {'PREHEAT': 'j--', 'HEAT': '---', 'SOAK': 'j--'}, kinds ['base'], path modes ['PREHEAT'], branching 0, right-only False
    * from `PREHEAT`: `PREHEAT:base(B=1)`
* cover `HEAT_L`: λ = 4/5, budget 1, admissible ['HEAT'], flags {'PREHEAT': '---', 'HEAT': 'j--', 'SOAK': '---'}, kinds ['base'], path modes ['HEAT'], branching 0, right-only False
    * from `HEAT`: `HEAT:base(B=1)`
* cover `SOAK_L`: λ = 4/5, budget 1, admissible ['SOAK'], flags {'PREHEAT': 'jdd', 'HEAT': '---', 'SOAK': 'j--'}, kinds ['base'], path modes ['SOAK'], branching 0, right-only False
    * from `SOAK`: `SOAK:base(B=1)`
* cells: **M1** yes: PREHEAT λ=4/5, HEAT λ=4/5, SOAK λ=4/5 (affine dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.PREHEAT: 3 conjunct(s); L.HEAT: 4 conjunct(s); L.SOAK: 4 conjunct(s); R.PREHEAT: 3 conjunct(s); R.HEAT: 4 conjunct(s); R.SOAK: 4 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape; L.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape; R.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape; R.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `gantry_speed_zones`

* family: Gantry speed zones (multi-cycle matching); scenario: controller-refinement; dims L/R 2/2; modes L/R 3/1; εL/εR 0.1/0.1; λ ∈ [1.0, 3.0]; invariant shape conjunctive; rows identical: True; normalized md5 `62c25fa54533`
* `relcert`: **CERTIFIED** (1250 ms); `[prune] gantry_speed_zones: []`; NO_PRUNE: **CERTIFIED** (1224 ms); NO_CUT: **CERTIFIED** (809 ms); NO_IMPLIED_CUT: **CERTIFIED** (821 ms); NO_LINEAR_CUT: **CERTIFIED** (1325 ms); domains: uniform
* `[cut] L.FREE: 4 conjunct(s)`
* `[cut] L.APPROACH: 4 conjunct(s)`
* `[cut] L.PLACE: 4 conjunct(s)`
* `[cut] R.MOVE: 4 conjunct(s)`
* `[cut-x] L.FREE: x <= 0.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.APPROACH: x <= 0.5 kind=implied-contraction entry=rational route=shape`
* `[admissible] FREE_L: [MOVE]`
* `[admissible] APPROACH_L: [MOVE]`
* `[admissible] PLACE_L: [MOVE]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (53 ms)
* cover `FREE_L`: λ = 3, budget 3, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base', 'joint'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:joint(B=3)->[MOVE@2, MOVE@2]; MOVE:joint(B=2)->[MOVE@1, MOVE@1]; MOVE:base(B=1)`
* cover `APPROACH_L`: λ = 2, budget 2, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base', 'joint'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:joint(B=2)->[MOVE@1, MOVE@1]; MOVE:base(B=1)`
* cover `PLACE_L`: λ = 1, budget 1, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:base(B=1)`
* cells: **M1** yes: FREE λ=3, APPROACH λ=2 (affine dynamics); **M2** yes: FREE B=3 via MOVE, APPROACH B=2 via MOVE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.FREE: 4 conjunct(s); L.APPROACH: 4 conjunct(s); L.PLACE: 4 conjunct(s); R.MOVE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.FREE: x <= 0.5 kind=implied-contraction entry=rational route=shape; L.APPROACH: x <= 0.5 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `h2_refuel_ambientbias`

* family: Hydrogen refuelling (sensor bias); scenario: sensor-fault (degraded sensor feeding the end-pressure table); dims L/R 1/1; modes L/R 5/5; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `b37cf62a5fba`
* `relcert`: **CERTIFIED** (617 ms); `[prune] h2_refuel_ambientbias: []`; NO_PRUNE: **CERTIFIED** (616 ms); NO_CUT: **DECLINED** (91 ms); NO_IMPLIED_CUT: **DECLINED** (381 ms); NO_LINEAR_CUT: **CERTIFIED** (601 ms); domains: uniform
* `[cut] L.STAGE1: 1 conjunct(s)`
* `[cut] L.STAGE2: 2 conjunct(s)`
* `[cut] L.STAGE3: 2 conjunct(s)`
* `[cut] L.TOPOFF: 2 conjunct(s)`
* `[cut] L.COMPLETE: 1 conjunct(s)`
* `[cut] R.STAGE1: 1 conjunct(s)`
* `[cut] R.STAGE2: 2 conjunct(s)`
* `[cut] R.STAGE3: 2 conjunct(s)`
* `[cut] R.TOPOFF: 2 conjunct(s)`
* `[cut] R.COMPLETE: 1 conjunct(s)`
* `[cut-x] L.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.TOPOFF: p <= 72.9 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.TOPOFF: p <= 70.5 kind=implied-contraction entry=rational route=shape`
* `[admissible] STAGE1_L: [STAGE1, STAGE2, STAGE3, TOPOFF, COMPLETE]`
* `[admissible] STAGE2_L: [STAGE2, STAGE3, TOPOFF, COMPLETE]`
* `[admissible] STAGE3_L: [STAGE3, TOPOFF, COMPLETE]`
* `[admissible] TOPOFF_L: [TOPOFF, COMPLETE]`
* `[admissible] COMPLETE_L: [TOPOFF, COMPLETE]`
* `--handoff`: 9/9 checked, 9 passed, failing -, non-vacuous (60 ms)
* cover `STAGE1_L`: λ = 1, budget 1, admissible ['STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE1`: `STAGE1:base(B=1)`
    * from `STAGE2`: `STAGE2:base(B=1)`
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `STAGE2_L`: λ = 1, budget 1, admissible ['STAGE2', 'STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': '-dd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'STAGE2', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE2`: `STAGE2:base(B=1)`
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `STAGE3_L`: λ = 1, budget 1, admissible ['STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': '-dd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `TOPOFF_L`: λ = 1, budget 1, admissible ['TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': '-dd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'TOPOFF'], branching 0, right-only False
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `COMPLETE_L`: λ = 1, budget 1, admissible ['TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'TOPOFF'], branching 0, right-only False
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 9/9 handoffs unsat, rows differ; **M6** yes: L.STAGE1: 1 conjunct(s); L.STAGE2: 2 conjunct(s); L.STAGE3: 2 conjunct(s); L.TOPOFF: 2 conjunct(s); L.COMPLETE: 1 conjunct(s); R.STAGE1: 1 conjunct(s); R.STAGE2: 2 conjunct(s); R.STAGE3: 2 conjunct(s); R.TOPOFF: 2 conjunct(s); R.COMPLETE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape; L.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape; L.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape; L.TOPOFF: p <= 72.9 kind=implied-contraction entry=rational route=shape; R.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape; R.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape; R.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape; R.TOPOFF: p <= 70.5 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `hydro_rejection_gatecal`

* family: Hydro unit load rejection; scenario: degraded-sensor; dims L/R 3/3; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `5adb83bdfa97`
* `relcert`: **CERTIFIED** (312 ms); `[prune] hydro_rejection_gatecal: []`; NO_PRUNE: **CERTIFIED** (405 ms); NO_CUT: **CERTIFIED** (363 ms); NO_IMPLIED_CUT: **CERTIFIED** (379 ms); NO_LINEAR_CUT: **CERTIFIED** (406 ms); domains: uniform
* `[cut] L.ONGRID: 5 conjunct(s)`
* `[cut] L.REJECT: 6 conjunct(s)`
* `[cut] R.ONGRID: 5 conjunct(s)`
* `[cut] R.REJECT: 6 conjunct(s)`
* `[admissible] ONGRID_L: [ONGRID]`
* `[admissible] REJECT_L: [REJECT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (94 ms)
* cover `ONGRID_L`: λ = 1, budget 1, admissible ['ONGRID'], flags {'ONGRID': 'j--', 'REJECT': '---'}, kinds ['base'], path modes ['ONGRID'], branching 0, right-only False
    * from `ONGRID`: `ONGRID:base(B=1)`
* cover `REJECT_L`: λ = 1, budget 1, admissible ['REJECT'], flags {'ONGRID': '---', 'REJECT': 'j--'}, kinds ['base'], path modes ['REJECT'], branching 0, right-only False
    * from `REJECT`: `REJECT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.ONGRID: 5 conjunct(s); L.REJECT: 6 conjunct(s); R.ONGRID: 5 conjunct(s); R.REJECT: 6 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_csf21_vehicle_bus`

* family: Literature; scenario: sensor-attack; dims L/R 3/3; modes L/R 6/12; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `f823904414fa`
* `relcert`: **CERTIFIED** (3275 ms); `[prune] lit_csf21_vehicle_bus: []`; NO_PRUNE: **CERTIFIED** (3199 ms); NO_CUT: **CERTIFIED** (3167 ms); NO_IMPLIED_CUT: **CERTIFIED** (3263 ms); NO_LINEAR_CUT: **CERTIFIED** (3294 ms); domains: uniform
* `[cut] L.AccCool: 1 conjunct(s)`
* `[cut] L.AccHeat: 1 conjunct(s)`
* `[cut] L.CoastCool: 2 conjunct(s)`
* `[cut] L.CoastHeat: 2 conjunct(s)`
* `[cut] R.AccCoolA: 1 conjunct(s)`
* `[cut] R.AccCoolT: 1 conjunct(s)`
* `[cut] R.AccHeatA: 1 conjunct(s)`
* `[cut] R.AccHeatT: 1 conjunct(s)`
* `[cut] R.CoastCoolA: 2 conjunct(s)`
* `[cut] R.CoastCoolT: 2 conjunct(s)`
* `[cut] R.CoastHeatA: 2 conjunct(s)`
* `[cut] R.CoastHeatT: 2 conjunct(s)`
* `[admissible] AccCool_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `[admissible] AccHeat_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `[admissible] CoastCool_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `[admissible] CoastHeat_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `[admissible] BrkCool_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `[admissible] BrkHeat_L: [AccCoolA, AccCoolT, AccHeatA, AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA, BrkHeatT]`
* `--handoff`: 24/24 checked, 24 passed, failing -, VACUOUS (identical rows) (47 ms)
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct(s); L.CoastCool: 2 conjunct(s); L.CoastHeat: 2 conjunct(s); R.AccCoolA: 1 conjunct(s); R.AccCoolT: 1 conjunct(s); R.AccHeatA: 1 conjunct(s); R.AccHeatT: 1 conjunct(s); R.CoastCoolA: 2 conjunct(s); R.CoastCoolT: 2 conjunct(s); R.CoastHeatA: 2 conjunct(s); R.CoastHeatT: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_csf21_vehicle_thermo`

* family: Literature; scenario: sensor-attack; dims L/R 3/3; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `bda79666f4dc`
* `relcert`: **CERTIFIED** (1756 ms); `[prune] lit_csf21_vehicle_thermo: []`; NO_PRUNE: **CERTIFIED** (1697 ms); NO_CUT: **CERTIFIED** (1568 ms); NO_IMPLIED_CUT: **CERTIFIED** (1689 ms); NO_LINEAR_CUT: **CERTIFIED** (1672 ms); domains: uniform
* `[cut] L.AccCool: 1 conjunct(s)`
* `[cut] L.AccHeat: 1 conjunct(s)`
* `[cut] L.CoastCool: 2 conjunct(s)`
* `[cut] L.CoastHeat: 2 conjunct(s)`
* `[cut] R.AccCool: 1 conjunct(s)`
* `[cut] R.AccHeat: 1 conjunct(s)`
* `[cut] R.CoastCool: 2 conjunct(s)`
* `[cut] R.CoastHeat: 2 conjunct(s)`
* `[admissible] AccCool_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `[admissible] AccHeat_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `[admissible] CoastCool_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `[admissible] CoastHeat_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `[admissible] BrkCool_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `[admissible] BrkHeat_L: [AccCool, AccHeat, CoastCool, CoastHeat, BrkCool, BrkHeat]`
* `--handoff`: 36/36 checked, 36 passed, failing -, VACUOUS (identical rows) (49 ms)
* cover `AccCool_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': 'j--', 'AccHeat': 'j--', 'CoastCool': '---', 'CoastHeat': '---', 'BrkCool': '---', 'BrkHeat': '---'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:base(B=1)`
    * from `AccHeat`: `AccHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `CoastHeat`: `CoastHeat:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `BrkHeat`: `BrkHeat:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
* cover `AccHeat_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': 'j--', 'AccHeat': 'j--', 'CoastCool': '---', 'CoastHeat': '---', 'BrkCool': '---', 'BrkHeat': '---'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:base(B=1)`
    * from `AccHeat`: `AccHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `CoastHeat`: `CoastHeat:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
    * from `BrkHeat`: `BrkHeat:hop(B=1,preJ)->[AccCool@1, AccHeat@1]; AccCool:base(B=1); AccHeat:base(B=1)`
* cover `CoastCool_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': '---', 'AccHeat': '---', 'CoastCool': 'j--', 'CoastHeat': 'j--', 'BrkCool': '---', 'BrkHeat': '---'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `AccHeat`: `AccHeat:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:base(B=1)`
    * from `CoastHeat`: `CoastHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `BrkHeat`: `BrkHeat:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
* cover `CoastHeat_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': '---', 'AccHeat': '---', 'CoastCool': 'j--', 'CoastHeat': 'j--', 'BrkCool': '---', 'BrkHeat': '---'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `AccHeat`: `AccHeat:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:base(B=1)`
    * from `CoastHeat`: `CoastHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
    * from `BrkHeat`: `BrkHeat:hop(B=1,preJ)->[CoastCool@1, CoastHeat@1]; CoastCool:base(B=1); CoastHeat:base(B=1)`
* cover `BrkCool_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': '---', 'AccHeat': '---', 'CoastCool': '---', 'CoastHeat': '---', 'BrkCool': 'j--', 'BrkHeat': 'j--'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `AccHeat`: `AccHeat:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `CoastHeat`: `CoastHeat:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:base(B=1)`
    * from `BrkHeat`: `BrkHeat:base(B=1)`
* cover `BrkHeat_L`: λ = 1, budget 1, admissible ['AccCool', 'AccHeat', 'CoastCool', 'CoastHeat', 'BrkCool', 'BrkHeat'], flags {'AccCool': '---', 'AccHeat': '---', 'CoastCool': '---', 'CoastHeat': '---', 'BrkCool': 'j--', 'BrkHeat': 'j--'}, kinds ['base', 'hop'], path modes ['AccCool', 'AccHeat', 'BrkCool', 'BrkHeat', 'CoastCool', 'CoastHeat'], branching 0, right-only False
    * from `AccCool`: `AccCool:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `AccHeat`: `AccHeat:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `CoastCool`: `CoastCool:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `CoastHeat`: `CoastHeat:hop(B=1,preJ)->[BrkCool@1, BrkHeat@1]; BrkCool:base(B=1); BrkHeat:base(B=1)`
    * from `BrkCool`: `BrkCool:base(B=1)`
    * from `BrkHeat`: `BrkHeat:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct(s); L.CoastCool: 2 conjunct(s); L.CoastHeat: 2 conjunct(s); R.AccCool: 1 conjunct(s); R.AccHeat: 1 conjunct(s); R.CoastCool: 2 conjunct(s); R.CoastHeat: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_csf25_salt_tank_hold`

* family: Literature; scenario: dos-attack; dims L/R 2/2; modes L/R 2/2; εL/εR 3.0/1.0; λ ∈ [0.3333333333, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `61de1ef64c38`
* `relcert`: **CERTIFIED** (294 ms); `[prune] lit_csf25_salt_tank_hold: []`; NO_PRUNE: **CERTIFIED** (244 ms); NO_CUT: **DECLINED** (1442 ms); NO_IMPLIED_CUT: **DECLINED** (1485 ms); NO_LINEAR_CUT: **CERTIFIED** (285 ms); domains: uniform
* `[cut] L.HoldInc: 3 conjunct(s)`
* `[cut] L.HoldDec: 3 conjunct(s)`
* `[cut] R.Inc: 1 conjunct(s)`
* `[cut] R.Dec: 1 conjunct(s)`
* `[cut-x] L.HoldInc: xp >= 36.43 kind=closure entry=weakening route=shape`
* `[cut-x] L.HoldInc: xp <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.HoldDec: xp <= 36.75 kind=closure entry=weakening route=shape`
* `[cut-x] L.HoldDec: xp >= 25.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.Inc: xp <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.Dec: xp >= 25.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] HoldInc_L: [Inc]`
* `[admissible] HoldDec_L: [Dec]`
* `--handoff`: 2/2 checked, 2 passed, failing -, non-vacuous (93 ms)
* cover `HoldInc_L`: λ = 1/3, budget 1, admissible ['Inc'], flags {'Inc': 'j--', 'Dec': '---'}, kinds ['base'], path modes ['Inc'], branching 0, right-only False
    * from `Inc`: `Inc:base(B=1)`
* cover `HoldDec_L`: λ = 1/3, budget 1, admissible ['Dec'], flags {'Inc': '---', 'Dec': 'j--'}, kinds ['base'], path modes ['Dec'], branching 0, right-only False
    * from `Dec`: `Dec:base(B=1)`
* cells: **M1** yes: HoldInc λ=1/3, HoldDec λ=1/3 (affine dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 2/2 handoffs unsat, rows differ; **M6** yes: L.HoldInc: 3 conjunct(s); L.HoldDec: 3 conjunct(s); R.Inc: 1 conjunct(s); R.Dec: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.HoldInc: xp >= 36.43 kind=closure entry=weakening route=shape; L.HoldInc: xp <= 100.0 kind=implied-contraction entry=rational route=shape; L.HoldDec: xp <= 36.75 kind=closure entry=weakening route=shape; L.HoldDec: xp >= 25.0 kind=implied-contraction entry=rational route=shape; R.Inc: xp <= 100.0 kind=implied-contraction entry=rational route=shape; R.Dec: xp >= 25.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `lit_drl_lane_control`

* family: Literature; scenario: controller-refinement; dims L/R 3/3; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0e06478ae77f`
* `relcert`: **CERTIFIED** (2670 ms); `[prune] lit_drl_lane_control: []`; NO_PRUNE: **CERTIFIED** (2662 ms); NO_CUT: **CERTIFIED** (2536 ms); NO_IMPLIED_CUT: **CERTIFIED** (2634 ms); NO_LINEAR_CUT: **CERTIFIED** (2700 ms); domains: uniform
* `[cut] L.AccelLAccel: 2 conjunct(s)`
* `[cut] L.AccelLBrake: 2 conjunct(s)`
* `[cut] L.CoastLAccel: 3 conjunct(s)`
* `[cut] L.CoastLBrake: 3 conjunct(s)`
* `[cut] L.BrakeLAccel: 2 conjunct(s)`
* `[cut] L.BrakeLBrake: 2 conjunct(s)`
* `[cut] R.AccelLAccel: 2 conjunct(s)`
* `[cut] R.AccelLBrake: 2 conjunct(s)`
* `[cut] R.CoastLAccel: 3 conjunct(s)`
* `[cut] R.CoastLBrake: 3 conjunct(s)`
* `[cut] R.BrakeLAccel: 2 conjunct(s)`
* `[cut] R.BrakeLBrake: 2 conjunct(s)`
* `[admissible] AccelLAccel_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `[admissible] AccelLBrake_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `[admissible] CoastLAccel_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `[admissible] CoastLBrake_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `[admissible] BrakeLAccel_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `[admissible] BrakeLBrake_L: [AccelLAccel, AccelLBrake, CoastLAccel, CoastLBrake, BrakeLAccel, BrakeLBrake]`
* `--handoff`: 36/36 checked, 36 passed, failing -, VACUOUS (identical rows) (165 ms)
* cover `AccelLAccel_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': 'j--', 'AccelLBrake': '---', 'CoastLAccel': '---', 'CoastLBrake': '---', 'BrakeLAccel': '---', 'BrakeLBrake': '---'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:hop(B=1,preJ)->[AccelLAccel@1]; AccelLAccel:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:hop(B=1,preJ)->[AccelLAccel@1]; AccelLAccel:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:hop(B=1,preJ)->[AccelLAccel@1]; AccelLAccel:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:hop(B=1,preJ)->[AccelLAccel@1]; AccelLAccel:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:hop(B=1,preJ)->[AccelLAccel@1]; AccelLAccel:base(B=1)`
* cover `AccelLBrake_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': '---', 'AccelLBrake': 'j--', 'CoastLAccel': '---', 'CoastLBrake': '---', 'BrakeLAccel': '---', 'BrakeLBrake': '---'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:hop(B=1,preJ)->[AccelLBrake@1]; AccelLBrake:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:hop(B=1,preJ)->[AccelLBrake@1]; AccelLBrake:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:hop(B=1,preJ)->[AccelLBrake@1]; AccelLBrake:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:hop(B=1,preJ)->[AccelLBrake@1]; AccelLBrake:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:hop(B=1,preJ)->[AccelLBrake@1]; AccelLBrake:base(B=1)`
* cover `CoastLAccel_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': '---', 'AccelLBrake': '---', 'CoastLAccel': 'j--', 'CoastLBrake': '---', 'BrakeLAccel': '---', 'BrakeLBrake': '---'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:hop(B=1,preJ)->[CoastLAccel@1]; CoastLAccel:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:hop(B=1,preJ)->[CoastLAccel@1]; CoastLAccel:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:hop(B=1,preJ)->[CoastLAccel@1]; CoastLAccel:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:hop(B=1,preJ)->[CoastLAccel@1]; CoastLAccel:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:hop(B=1,preJ)->[CoastLAccel@1]; CoastLAccel:base(B=1)`
* cover `CoastLBrake_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': '---', 'AccelLBrake': '---', 'CoastLAccel': '---', 'CoastLBrake': 'j--', 'BrakeLAccel': '---', 'BrakeLBrake': '---'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:hop(B=1,preJ)->[CoastLBrake@1]; CoastLBrake:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:hop(B=1,preJ)->[CoastLBrake@1]; CoastLBrake:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:hop(B=1,preJ)->[CoastLBrake@1]; CoastLBrake:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:hop(B=1,preJ)->[CoastLBrake@1]; CoastLBrake:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:hop(B=1,preJ)->[CoastLBrake@1]; CoastLBrake:base(B=1)`
* cover `BrakeLAccel_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': '---', 'AccelLBrake': '---', 'CoastLAccel': '---', 'CoastLBrake': '---', 'BrakeLAccel': 'j--', 'BrakeLBrake': '---'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:hop(B=1,preJ)->[BrakeLAccel@1]; BrakeLAccel:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:hop(B=1,preJ)->[BrakeLAccel@1]; BrakeLAccel:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:hop(B=1,preJ)->[BrakeLAccel@1]; BrakeLAccel:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:hop(B=1,preJ)->[BrakeLAccel@1]; BrakeLAccel:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:hop(B=1,preJ)->[BrakeLAccel@1]; BrakeLAccel:base(B=1)`
* cover `BrakeLBrake_L`: λ = 1, budget 1, admissible ['AccelLAccel', 'AccelLBrake', 'CoastLAccel', 'CoastLBrake', 'BrakeLAccel', 'BrakeLBrake'], flags {'AccelLAccel': '---', 'AccelLBrake': '---', 'CoastLAccel': '---', 'CoastLBrake': '---', 'BrakeLAccel': '---', 'BrakeLBrake': 'j--'}, kinds ['base', 'hop'], path modes ['AccelLAccel', 'AccelLBrake', 'BrakeLAccel', 'BrakeLBrake', 'CoastLAccel', 'CoastLBrake'], branching 0, right-only False
    * from `AccelLAccel`: `AccelLAccel:hop(B=1,preJ)->[BrakeLBrake@1]; BrakeLBrake:base(B=1)`
    * from `AccelLBrake`: `AccelLBrake:hop(B=1,preJ)->[BrakeLBrake@1]; BrakeLBrake:base(B=1)`
    * from `CoastLAccel`: `CoastLAccel:hop(B=1,preJ)->[BrakeLBrake@1]; BrakeLBrake:base(B=1)`
    * from `CoastLBrake`: `CoastLBrake:hop(B=1,preJ)->[BrakeLBrake@1]; BrakeLBrake:base(B=1)`
    * from `BrakeLAccel`: `BrakeLAccel:hop(B=1,preJ)->[BrakeLBrake@1]; BrakeLBrake:base(B=1)`
    * from `BrakeLBrake`: `BrakeLBrake:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.AccelLAccel: 2 conjunct(s); L.AccelLBrake: 2 conjunct(s); L.CoastLAccel: 3 conjunct(s); L.CoastLBrake: 3 conjunct(s); L.BrakeLAccel: 2 conjunct(s); L.BrakeLBrake: 2 conjunct(s); R.AccelLAccel: 2 conjunct(s); R.AccelLBrake: 2 conjunct(s); R.CoastLAccel: 3 conjunct(s); R.CoastLBrake: 3 conjunct(s); R.BrakeLAccel: 2 conjunct(s); R.BrakeLBrake: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_freedm_meter`

* family: Literature; scenario: information-flow; dims L/R 2/2; modes L/R 12/12; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `956055de14c2`
* `relcert`: **CERTIFIED** (2292 ms); `[prune] lit_freedm_meter: []`; NO_PRUNE: **CERTIFIED** (2313 ms); NO_CUT: **CERTIFIED** (2360 ms); NO_IMPLIED_CUT: **CERTIFIED** (2291 ms); NO_LINEAR_CUT: **CERTIFIED** (2312 ms); domains: uniform
* `[cut] L.BatD0R0: 2 conjunct(s)`
* `[cut] L.BatD0R1: 1 conjunct(s)`
* `[cut] L.BatD1R0: 1 conjunct(s)`
* `[cut] L.BatD1R1: 2 conjunct(s)`
* `[cut] L.BatD2R0: 1 conjunct(s)`
* `[cut] L.BatD2R1: 1 conjunct(s)`
* `[cut] L.GridD0R0: 2 conjunct(s)`
* `[cut] L.GridD0R1: 2 conjunct(s)`
* `[cut] L.GridD1R0: 2 conjunct(s)`
* `[cut] L.GridD1R1: 2 conjunct(s)`
* `[cut] L.GridD2R0: 2 conjunct(s)`
* `[cut] L.GridD2R1: 2 conjunct(s)`
* `[cut] R.BatD0R0: 2 conjunct(s)`
* `[cut] R.BatD0R1: 1 conjunct(s)`
* `[cut] R.BatD1R0: 1 conjunct(s)`
* `[cut] R.BatD1R1: 2 conjunct(s)`
* `[cut] R.BatD2R0: 1 conjunct(s)`
* `[cut] R.BatD2R1: 1 conjunct(s)`
* `[cut] R.GridD0R0: 2 conjunct(s)`
* `[cut] R.GridD0R1: 2 conjunct(s)`
* `[cut] R.GridD1R0: 2 conjunct(s)`
* `[cut] R.GridD1R1: 2 conjunct(s)`
* `[cut] R.GridD2R0: 2 conjunct(s)`
* `[cut] R.GridD2R1: 2 conjunct(s)`
* `[cut-x] L.BatD0R0: B <= 10.0 kind=closure entry=weakening route=frozen`
* `[cut-x] L.BatD1R1: B <= 10.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.BatD0R0: B <= 10.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.BatD1R1: B <= 10.0 kind=closure entry=weakening route=frozen`
* `[admissible] BatD0R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] BatD0R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] BatD1R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] BatD1R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] BatD2R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] BatD2R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD0R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD0R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD1R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD1R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD2R0_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `[admissible] GridD2R1_L: [BatD0R0, BatD0R1, BatD1R0, BatD1R1, BatD2R0, BatD2R1, GridD0R0, GridD0R1, GridD1R0, GridD1R1, GridD2R0, GridD2R1]`
* `--handoff`: 144/144 checked, 144 passed, failing -, VACUOUS (identical rows) (188 ms)
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.BatD0R0: 2 conjunct(s); L.BatD0R1: 1 conjunct(s); L.BatD1R0: 1 conjunct(s); L.BatD1R1: 2 conjunct(s); L.BatD2R0: 1 conjunct(s); L.BatD2R1: 1 conjunct(s); L.GridD0R0: 2 conjunct(s); L.GridD0R1: 2 conjunct(s); L.GridD1R0: 2 conjunct(s); L.GridD1R1: 2 conjunct(s); L.GridD2R0: 2 conjunct(s); L.GridD2R1: 2 conjunct(s); R.BatD0R0: 2 conjunct(s); R.BatD0R1: 1 conjunct(s); R.BatD1R0: 1 conjunct(s); R.BatD1R1: 2 conjunct(s); R.BatD2R0: 1 conjunct(s); R.BatD2R1: 1 conjunct(s); R.GridD0R0: 2 conjunct(s); R.GridD0R1: 2 conjunct(s); R.GridD1R0: 2 conjunct(s); R.GridD1R1: 2 conjunct(s); R.GridD2R0: 2 conjunct(s); R.GridD2R1: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.BatD0R0: B <= 10.0 kind=closure entry=weakening route=frozen; L.BatD1R1: B <= 10.0 kind=closure entry=weakening route=frozen; R.BatD0R0: B <= 10.0 kind=closure entry=weakening route=frozen; R.BatD1R1: B <= 10.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `lit_girard08_robot`

* family: Literature; scenario: abstraction; dims L/R 6/2; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic+conj; rows identical: True; normalized md5 `43a1cc56b6e5`
* `relcert`: **CERTIFIED** (53551 ms); `[prune] lit_girard08_robot: []`; NO_PRUNE: **CERTIFIED** (53075 ms); NO_CUT: **CERTIFIED** (35675 ms); NO_IMPLIED_CUT: **CERTIFIED** (52797 ms); NO_LINEAR_CUT: **CERTIFIED** (52716 ms); domains: uniform
* `[cut] R.M1: 2 conjunct(s)`
* `[cut] R.M2: 1 conjunct(s)`
* `[cut] R.M3: 1 conjunct(s)`
* `[cut] R.M4: 2 conjunct(s)`
* `[cut] R.M5: 1 conjunct(s)`
* `[cut] R.M6: 1 conjunct(s)`
* `[admissible] M1_L: [M1, M2, M3, M4, M6]`
* `[admissible] M2_L: [M1, M2, M3]`
* `[admissible] M3_L: [M1, M2, M3, M4, M6]`
* `[admissible] M4_L: [M1, M3, M4, M5, M6]`
* `[admissible] M5_L: [M4, M5, M6]`
* `[admissible] M6_L: [M1, M3, M4, M5, M6]`
* `--handoff`: 12/12 checked, 12 passed, failing -, VACUOUS (identical rows) (108 ms)
* cover `M1_L`: λ = 1, budget 1, admissible ['M1', 'M2', 'M3', 'M4', 'M6'], flags {'M1': 'j--', 'M2': '---', 'M3': '---', 'M4': '---', 'M5': '---', 'M6': '---'}, kinds ['base', 'hop'], path modes ['M1', 'M2', 'M3', 'M4', 'M6'], branching 0, right-only False
    * from `M1`: `M1:base(B=1)`
    * from `M2`: `M2:hop(B=1,preJ)->[M1@1]; M1:base(B=1)`
    * from `M3`: `M3:hop(B=1,preJ)->[M1@1]; M1:base(B=1)`
    * from `M4`: `M4:hop(B=1,preJ)->[M1@1]; M1:base(B=1)`
    * from `M6`: `M6:hop(B=1,preJ)->[M1@1]; M1:base(B=1)`
* cover `M2_L`: λ = 1, budget 1, admissible ['M1', 'M2', 'M3'], flags {'M1': '---', 'M2': 'j--', 'M3': '---', 'M4': '---', 'M5': '---', 'M6': '---'}, kinds ['base', 'hop'], path modes ['M1', 'M2', 'M3'], branching 0, right-only False
    * from `M1`: `M1:hop(B=1,preJ)->[M2@1]; M2:base(B=1)`
    * from `M2`: `M2:base(B=1)`
    * from `M3`: `M3:hop(B=1,preJ)->[M2@1]; M2:base(B=1)`
* cover `M3_L`: λ = 1, budget 1, admissible ['M1', 'M2', 'M3', 'M4', 'M6'], flags {'M1': '---', 'M2': '---', 'M3': 'j--', 'M4': '---', 'M5': '---', 'M6': '---'}, kinds ['base', 'hop'], path modes ['M1', 'M2', 'M3', 'M4', 'M6'], branching 0, right-only False
    * from `M1`: `M1:hop(B=1,preJ)->[M3@1]; M3:base(B=1)`
    * from `M2`: `M2:hop(B=1,preJ)->[M3@1]; M3:base(B=1)`
    * from `M3`: `M3:base(B=1)`
    * from `M4`: `M4:hop(B=1,preJ)->[M3@1]; M3:base(B=1)`
    * from `M6`: `M6:hop(B=1,preJ)->[M3@1]; M3:base(B=1)`
* cover `M4_L`: λ = 1, budget 1, admissible ['M1', 'M3', 'M4', 'M5', 'M6'], flags {'M1': '---', 'M2': '---', 'M3': '---', 'M4': 'j--', 'M5': '---', 'M6': '---'}, kinds ['base', 'hop'], path modes ['M1', 'M3', 'M4', 'M5', 'M6'], branching 0, right-only False
    * from `M1`: `M1:hop(B=1,preJ)->[M4@1]; M4:base(B=1)`
    * from `M3`: `M3:hop(B=1,preJ)->[M4@1]; M4:base(B=1)`
    * from `M4`: `M4:base(B=1)`
    * from `M5`: `M5:hop(B=1,preJ)->[M4@1]; M4:base(B=1)`
    * from `M6`: `M6:hop(B=1,preJ)->[M4@1]; M4:base(B=1)`
* cover `M5_L`: λ = 1, budget 1, admissible ['M4', 'M5', 'M6'], flags {'M1': '---', 'M2': '---', 'M3': '---', 'M4': '---', 'M5': 'j--', 'M6': '---'}, kinds ['base', 'hop'], path modes ['M4', 'M5', 'M6'], branching 0, right-only False
    * from `M4`: `M4:hop(B=1,preJ)->[M5@1]; M5:base(B=1)`
    * from `M5`: `M5:base(B=1)`
    * from `M6`: `M6:hop(B=1,preJ)->[M5@1]; M5:base(B=1)`
* cover `M6_L`: λ = 1, budget 1, admissible ['M1', 'M3', 'M4', 'M5', 'M6'], flags {'M1': '---', 'M2': '---', 'M3': '---', 'M4': '---', 'M5': '---', 'M6': 'j--'}, kinds ['base', 'hop'], path modes ['M1', 'M3', 'M4', 'M5', 'M6'], branching 0, right-only False
    * from `M1`: `M1:hop(B=1,preJ)->[M6@1]; M6:base(B=1)`
    * from `M3`: `M3:hop(B=1,preJ)->[M6@1]; M6:base(B=1)`
    * from `M4`: `M4:hop(B=1,preJ)->[M6@1]; M6:base(B=1)`
    * from `M5`: `M5:hop(B=1,preJ)->[M6@1]; M6:base(B=1)`
    * from `M6`: `M6:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (R.M1: 2 conjunct(s); R.M2: 1 conjunct(s); R.M3: 1 conjunct(s); R.M4: 2 conjunct(s); R.M5: 1 conjunct(s); R.M6: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_gpt10_boost_converter`

* family: Literature; scenario: abstraction; dims L/R 2/2; modes L/R 48/2; εL/εR 0.5/0.5; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `678546c5b237`
* `relcert`: **CERTIFIED** (50932 ms); `[prune] lit_gpt10_boost_converter: []`; NO_PRUNE: **CERTIFIED** (50674 ms); NO_CUT: **CERTIFIED** (51287 ms); NO_IMPLIED_CUT: **CERTIFIED** (51154 ms); NO_LINEAR_CUT: **CERTIFIED** (50736 ms); domains: uniform
* `[cut] L.P1d00: 1 conjunct(s)`
* `[cut] L.P1d01: 1 conjunct(s)`
* `[cut] L.P1d02: 1 conjunct(s)`
* `[cut] L.P1d03: 1 conjunct(s)`
* `[cut] L.P1d04: 1 conjunct(s)`
* `[cut] L.P1d05: 1 conjunct(s)`
* `[cut] L.P1d06: 1 conjunct(s)`
* `[cut] L.P1d07: 1 conjunct(s)`
* `[cut] L.P1d08: 1 conjunct(s)`
* `[cut] L.P1d09: 1 conjunct(s)`
* `[cut] L.P1d10: 1 conjunct(s)`
* `[cut] L.P1d11: 1 conjunct(s)`
* `[cut] L.P1d12: 1 conjunct(s)`
* `[cut] L.P1d13: 1 conjunct(s)`
* `[cut] L.P1d14: 1 conjunct(s)`
* `[cut] L.P1d15: 1 conjunct(s)`
* `[cut] L.P1d16: 1 conjunct(s)`
* `[cut] L.P1d17: 1 conjunct(s)`
* `[cut] L.P1d18: 1 conjunct(s)`
* `[cut] L.P1d19: 1 conjunct(s)`
* `[cut] L.P1d20: 1 conjunct(s)`
* `[cut] L.P1d21: 1 conjunct(s)`
* `[cut] L.P1d22: 1 conjunct(s)`
* `[cut] L.P1d23: 1 conjunct(s)`
* `[cut] L.P2d00: 1 conjunct(s)`
* `[cut] L.P2d01: 1 conjunct(s)`
* `[cut] L.P2d02: 1 conjunct(s)`
* `[cut] L.P2d03: 1 conjunct(s)`
* `[cut] L.P2d04: 1 conjunct(s)`
* `[cut] L.P2d05: 1 conjunct(s)`
* `[cut] L.P2d06: 1 conjunct(s)`
* `[cut] L.P2d07: 1 conjunct(s)`
* `[cut] L.P2d08: 1 conjunct(s)`
* `[cut] L.P2d09: 1 conjunct(s)`
* `[cut] L.P2d10: 1 conjunct(s)`
* `[cut] L.P2d11: 1 conjunct(s)`
* `[cut] L.P2d12: 1 conjunct(s)`
* `[cut] L.P2d13: 1 conjunct(s)`
* `[cut] L.P2d14: 1 conjunct(s)`
* `[cut] L.P2d15: 1 conjunct(s)`
* `[cut] L.P2d16: 1 conjunct(s)`
* `[cut] L.P2d17: 1 conjunct(s)`
* `[cut] L.P2d18: 1 conjunct(s)`
* `[cut] L.P2d19: 1 conjunct(s)`
* `[cut] L.P2d20: 1 conjunct(s)`
* `[cut] L.P2d21: 1 conjunct(s)`
* `[cut] L.P2d22: 1 conjunct(s)`
* `[cut] L.P2d23: 1 conjunct(s)`
* `[cut] R.P1: 1 conjunct(s)`
* `[cut] R.P2: 1 conjunct(s)`
* `[admissible] P1d00_L: [P1, P2]`
* `[admissible] P1d01_L: [P1, P2]`
* `[admissible] P1d02_L: [P1, P2]`
* `[admissible] P1d03_L: [P1, P2]`
* `[admissible] P1d04_L: [P1, P2]`
* `[admissible] P1d05_L: [P1, P2]`
* `[admissible] P1d06_L: [P1, P2]`
* `[admissible] P1d07_L: [P1, P2]`
* `[admissible] P1d08_L: [P1, P2]`
* `[admissible] P1d09_L: [P1, P2]`
* `[admissible] P1d10_L: [P1, P2]`
* `[admissible] P1d11_L: [P1, P2]`
* `[admissible] P1d12_L: [P1, P2]`
* `[admissible] P1d13_L: [P1, P2]`
* `[admissible] P1d14_L: [P1, P2]`
* `[admissible] P1d15_L: [P1, P2]`
* `[admissible] P1d16_L: [P1, P2]`
* `[admissible] P1d17_L: [P1, P2]`
* `[admissible] P1d18_L: [P1, P2]`
* `[admissible] P1d19_L: [P1, P2]`
* `[admissible] P1d20_L: [P1, P2]`
* `[admissible] P1d21_L: [P1, P2]`
* `[admissible] P1d22_L: [P1, P2]`
* `[admissible] P1d23_L: [P1, P2]`
* `[admissible] P2d00_L: [P1, P2]`
* `[admissible] P2d01_L: [P1, P2]`
* `[admissible] P2d02_L: [P1, P2]`
* `[admissible] P2d03_L: [P1, P2]`
* `[admissible] P2d04_L: [P1, P2]`
* `[admissible] P2d05_L: [P1, P2]`
* `[admissible] P2d06_L: [P1, P2]`
* `[admissible] P2d07_L: [P1, P2]`
* `[admissible] P2d08_L: [P1, P2]`
* `[admissible] P2d09_L: [P1, P2]`
* `[admissible] P2d10_L: [P1, P2]`
* `[admissible] P2d11_L: [P1, P2]`
* `[admissible] P2d12_L: [P1, P2]`
* `[admissible] P2d13_L: [P1, P2]`
* `[admissible] P2d14_L: [P1, P2]`
* `[admissible] P2d15_L: [P1, P2]`
* `[admissible] P2d16_L: [P1, P2]`
* `[admissible] P2d17_L: [P1, P2]`
* `[admissible] P2d18_L: [P1, P2]`
* `[admissible] P2d19_L: [P1, P2]`
* `[admissible] P2d20_L: [P1, P2]`
* `[admissible] P2d21_L: [P1, P2]`
* `[admissible] P2d22_L: [P1, P2]`
* `[admissible] P2d23_L: [P1, P2]`
* `--handoff`: 2304/2304 checked, 2304 passed, failing -, VACUOUS (identical rows) (1426 ms)
* cover `P1d00_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d01_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d02_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d03_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d04_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d05_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d06_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d07_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d08_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d09_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d10_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d11_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d12_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d13_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d14_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d15_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d16_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d17_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d18_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d19_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d20_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d21_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d22_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P1d23_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': 'j--', 'P2': '---'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:base(B=1)`
    * from `P2`: `P2:hop(B=1,preJ)->[P1@1]; P1:base(B=1)`
* cover `P2d00_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d01_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d02_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d03_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d04_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d05_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d06_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d07_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d08_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d09_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d10_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d11_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d12_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d13_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d14_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d15_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d16_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d17_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d18_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d19_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d20_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d21_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d22_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cover `P2d23_L`: λ = 1, budget 1, admissible ['P1', 'P2'], flags {'P1': '---', 'P2': 'j--'}, kinds ['base', 'hop'], path modes ['P1', 'P2'], branching 0, right-only False
    * from `P1`: `P1:hop(B=1,preJ)->[P2@1]; P2:base(B=1)`
    * from `P2`: `P2:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.P1d00: 1 conjunct(s); L.P1d01: 1 conjunct(s); L.P1d02: 1 conjunct(s); L.P1d03: 1 conjunct(s); L.P1d04: 1 conjunct(s); L.P1d05: 1 conjunct(s); L.P1d06: 1 conjunct(s); L.P1d07: 1 conjunct(s); L.P1d08: 1 conjunct(s); L.P1d09: 1 conjunct(s); L.P1d10: 1 conjunct(s); L.P1d11: 1 conjunct(s); L.P1d12: 1 conjunct(s); L.P1d13: 1 conjunct(s); L.P1d14: 1 conjunct(s); L.P1d15: 1 conjunct(s); L.P1d16: 1 conjunct(s); L.P1d17: 1 conjunct(s); L.P1d18: 1 conjunct(s); L.P1d19: 1 conjunct(s); L.P1d20: 1 conjunct(s); L.P1d21: 1 conjunct(s); L.P1d22: 1 conjunct(s); L.P1d23: 1 conjunct(s); L.P2d00: 1 conjunct(s); L.P2d01: 1 conjunct(s); L.P2d02: 1 conjunct(s); L.P2d03: 1 conjunct(s); L.P2d04: 1 conjunct(s); L.P2d05: 1 conjunct(s); L.P2d06: 1 conjunct(s); L.P2d07: 1 conjunct(s); L.P2d08: 1 conjunct(s); L.P2d09: 1 conjunct(s); L.P2d10: 1 conjunct(s); L.P2d11: 1 conjunct(s); L.P2d12: 1 conjunct(s); L.P2d13: 1 conjunct(s); L.P2d14: 1 conjunct(s); L.P2d15: 1 conjunct(s); L.P2d16: 1 conjunct(s); L.P2d17: 1 conjunct(s); L.P2d18: 1 conjunct(s); L.P2d19: 1 conjunct(s); L.P2d20: 1 conjunct(s); L.P2d21: 1 conjunct(s); L.P2d22: 1 conjunct(s); L.P2d23: 1 conjunct(s); R.P1: 1 conjunct(s); R.P2: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_lz21_vehicle_position`

* family: Literature; scenario: opacity; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `3998cc4c0e75`
* `relcert`: **CERTIFIED** (413 ms); `[prune] lit_lz21_vehicle_position: []`; NO_PRUNE: **CERTIFIED** (393 ms); NO_CUT: **CERTIFIED** (403 ms); NO_IMPLIED_CUT: **CERTIFIED** (431 ms); NO_LINEAR_CUT: **CERTIFIED** (426 ms); domains: uniform
* `[cut] L.Um: 1 conjunct(s)`
* `[cut] L.U0: 2 conjunct(s)`
* `[cut] L.Up: 1 conjunct(s)`
* `[cut] R.Um: 1 conjunct(s)`
* `[cut] R.U0: 2 conjunct(s)`
* `[cut] R.Up: 1 conjunct(s)`
* `[admissible] Um_L: [Um, U0, Up]`
* `[admissible] U0_L: [Um, U0, Up]`
* `[admissible] Up_L: [Um, U0, Up]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (106 ms)
* cover `Um_L`: λ = 1, budget 1, admissible ['Um', 'U0', 'Up'], flags {'Um': 'j--', 'U0': '---', 'Up': '---'}, kinds ['base', 'hop'], path modes ['U0', 'Um', 'Up'], branching 0, right-only False
    * from `Um`: `Um:base(B=1)`
    * from `U0`: `U0:hop(B=1,preJ)->[Um@1]; Um:base(B=1)`
    * from `Up`: `Up:hop(B=1,preJ)->[Um@1]; Um:base(B=1)`
* cover `U0_L`: λ = 1, budget 1, admissible ['Um', 'U0', 'Up'], flags {'Um': '---', 'U0': 'j--', 'Up': '---'}, kinds ['base', 'hop'], path modes ['U0', 'Um', 'Up'], branching 0, right-only False
    * from `Um`: `Um:hop(B=1,preJ)->[U0@1]; U0:base(B=1)`
    * from `U0`: `U0:base(B=1)`
    * from `Up`: `Up:hop(B=1,preJ)->[U0@1]; U0:base(B=1)`
* cover `Up_L`: λ = 1, budget 1, admissible ['Um', 'U0', 'Up'], flags {'Um': '---', 'U0': '---', 'Up': 'j--'}, kinds ['base', 'hop'], path modes ['U0', 'Um', 'Up'], branching 0, right-only False
    * from `Um`: `Um:hop(B=1,preJ)->[Up@1]; Up:base(B=1)`
    * from `U0`: `U0:hop(B=1,preJ)->[Up@1]; Up:base(B=1)`
    * from `Up`: `Up:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Um: 1 conjunct(s); L.U0: 2 conjunct(s); L.Up: 1 conjunct(s); R.Um: 1 conjunct(s); R.U0: 2 conjunct(s); R.Up: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_nahs25_salt_tank`

* family: Literature; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/2; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8e01810795c4`
* `relcert`: **CERTIFIED** (197 ms); `[prune] lit_nahs25_salt_tank: []`; NO_PRUNE: **CERTIFIED** (134 ms); NO_CUT: **CERTIFIED** (250 ms); NO_IMPLIED_CUT: **CERTIFIED** (221 ms); NO_LINEAR_CUT: **CERTIFIED** (180 ms); domains: uniform
* `[cut] L.On: 1 conjunct(s)`
* `[cut] L.Off: 1 conjunct(s)`
* `[cut] R.On: 1 conjunct(s)`
* `[cut] R.Off: 1 conjunct(s)`
* `[cut-x] L.Off: xp <= 28.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.Off: xp <= 25.0 kind=closure entry=weakening route=frozen`
* `[admissible] On_L: [On]`
* `[admissible] Off_L: [On]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `On_L`: λ = 1, budget 1, admissible ['On'], flags {'On': 'j--', 'Off': 'jdd'}, kinds ['base'], path modes ['On'], branching 0, right-only False
    * from `On`: `On:base(B=1)`
* cover `Off_L`: λ = 1, budget 1, admissible ['On'], flags {'On': 'j--', 'Off': 'jdd'}, kinds ['base'], path modes ['On'], branching 0, right-only False
    * from `On`: `On:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.On: 1 conjunct(s); L.Off: 1 conjunct(s); R.On: 1 conjunct(s); R.Off: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.Off: xp <= 28.0 kind=closure entry=weakening route=frozen; R.Off: xp <= 25.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `molding_pack_checkring`

* family: Injection molding pack and hold; scenario: degraded-actuator; dims L/R 3/3; modes L/R 2/2; εL/εR 0.05/0.05; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `9778b9818220`
* `relcert`: **CERTIFIED** (398 ms); `[prune] molding_pack_checkring: []`; NO_PRUNE: **CERTIFIED** (390 ms); NO_CUT: **CERTIFIED** (306 ms); NO_IMPLIED_CUT: **CERTIFIED** (405 ms); NO_LINEAR_CUT: **CERTIFIED** (410 ms); domains: uniform
* `[cut] L.HOLD: 3 conjunct(s)`
* `[cut] L.COOL: 4 conjunct(s)`
* `[cut] R.HOLD: 3 conjunct(s)`
* `[cut] R.COOL: 4 conjunct(s)`
* `[admissible] HOLD_L: [HOLD]`
* `[admissible] COOL_L: [COOL]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (74 ms)
* cover `HOLD_L`: λ = 1, budget 1, admissible ['HOLD'], flags {'HOLD': 'j--', 'COOL': '---'}, kinds ['base'], path modes ['HOLD'], branching 0, right-only False
    * from `HOLD`: `HOLD:base(B=1)`
* cover `COOL_L`: λ = 1, budget 1, admissible ['COOL'], flags {'HOLD': '---', 'COOL': 'j--'}, kinds ['base'], path modes ['COOL'], branching 0, right-only False
    * from `COOL`: `COOL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.HOLD: 3 conjunct(s); L.COOL: 4 conjunct(s); R.HOLD: 3 conjunct(s); R.COOL: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `platoon_latency`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: degraded-network; dims L/R 3/3; modes L/R 2/1; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `fb8c5031920c`
* `relcert`: **CERTIFIED** (395 ms); `[prune] platoon_latency: []`; NO_PRUNE: **CERTIFIED** (449 ms); NO_CUT: **CERTIFIED** (393 ms); NO_IMPLIED_CUT: **CERTIFIED** (468 ms); NO_LINEAR_CUT: **CERTIFIED** (382 ms); domains: uniform
* `[cut] R.CACC: 4 conjunct(s)`
* `[admissible] CACC_UP_L: [CACC]`
* `[admissible] CACC_DN_L: [CACC]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `CACC_UP_L`: λ = 1, budget 1, admissible ['CACC'], flags {'CACC': 'j--'}, kinds ['base'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:base(B=1)`
* cover `CACC_DN_L`: λ = 1, budget 1, admissible ['CACC'], flags {'CACC': 'j--'}, kinds ['base'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (R.CACC: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `platoon_linkloss`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: dos-attack; dims L/R 2/2; modes L/R 2/1; εL/εR 0.2/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `d44483ae9f27`
* `relcert`: **CERTIFIED** (253 ms); `[prune] platoon_linkloss: []`; NO_PRUNE: **CERTIFIED** (304 ms); NO_CUT: **CERTIFIED** (283 ms); NO_IMPLIED_CUT: **CERTIFIED** (293 ms); NO_LINEAR_CUT: **CERTIFIED** (277 ms); domains: uniform
* `[cut] L.CACC: 4 conjunct(s)`
* `[cut] L.ACC: 4 conjunct(s)`
* `[cut] R.CACC: 4 conjunct(s)`
* `[admissible] CACC_L: [CACC]`
* `[admissible] ACC_L: [CACC]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (83 ms)
* cover `CACC_L`: λ = 1, budget 2, admissible ['CACC'], flags {'CACC': 'j--'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cover `ACC_L`: λ = 1, budget 2, admissible ['CACC'], flags {'CACC': 'j--'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: CACC B=2 via CACC, ACC B=2 via CACC; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CACC: 4 conjunct(s); L.ACC: 4 conjunct(s); R.CACC: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `platoon_profiles`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: controller-refinement; dims L/R 2/2; modes L/R 1/1; εL/εR 0.1/0.1; λ ∈ [1.2, 1.2]; invariant shape conjunctive; rows identical: True; normalized md5 `fe1c59494b3d`
* `relcert`: **CERTIFIED** (220 ms); `[prune] platoon_profiles: []`; NO_PRUNE: **CERTIFIED** (202 ms); NO_CUT: **CERTIFIED** (214 ms); NO_IMPLIED_CUT: **CERTIFIED** (133 ms); NO_LINEAR_CUT: **CERTIFIED** (148 ms); domains: uniform
* `[cut] L.SPORT: 4 conjunct(s)`
* `[cut] R.CACC: 4 conjunct(s)`
* `[admissible] SPORT_L: [CACC]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (80 ms)
* cover `SPORT_L`: λ = 6/5, budget 2, admissible ['CACC'], flags {'CACC': 'j--'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cells: **M1** yes: SPORT λ=6/5 (affine dynamics); **M2** yes: SPORT B=2 via CACC; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.SPORT: 4 conjunct(s); R.CACC: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `quad_light_lag`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 3/3; modes L/R 1/1; εL/εR 1.0/1.0; λ ∈ [1.2, 1.2]; invariant shape conjunctive; rows identical: True; normalized md5 `0a4a60039676`
* `relcert`: **CERTIFIED** (169 ms); `[prune] quad_light_lag: []`; NO_PRUNE: **CERTIFIED** (159 ms); NO_CUT: **CERTIFIED** (162 ms); NO_IMPLIED_CUT: **CERTIFIED** (170 ms); NO_LINEAR_CUT: **CERTIFIED** (91 ms); domains: uniform
* `[cut] L.CLIMB: 4 conjunct(s)`
* `[cut] R.CLIMB: 3 conjunct(s)`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (45 ms)
* cover `CLIMB_L`: λ = 6/5, budget 2, admissible ['CLIMB'], flags {'CLIMB': 'j--'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=6/5 (affine dynamics); **M2** yes: CLIMB B=2 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 4 conjunct(s); R.CLIMB: 3 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `quad_light_profiles`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.15, 1.25]; invariant shape conjunctive; rows identical: True; normalized md5 `af26e8672431`
* `relcert`: **CERTIFIED** (10041 ms); `[prune] quad_light_profiles: []`; NO_PRUNE: **CERTIFIED** (10129 ms); NO_CUT: **CERTIFIED** (10033 ms); NO_IMPLIED_CUT: **CERTIFIED** (10205 ms); NO_LINEAR_CUT: **CERTIFIED** (10234 ms); domains: uniform
* `[cut] L.ECO: 3 conjunct(s)`
* `[cut] L.NORMAL: 3 conjunct(s)`
* `[cut] L.SPORT: 3 conjunct(s)`
* `[cut] R.NORMAL: 3 conjunct(s)`
* `[cut] R.ECO: 3 conjunct(s)`
* `[cut] R.SPORT: 3 conjunct(s)`
* `[admissible] ECO_L: [NORMAL, ECO, SPORT]`
* `[admissible] NORMAL_L: [NORMAL, ECO, SPORT]`
* `[admissible] SPORT_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (110 ms)
* cover `ECO_L`: λ = 5/4, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': '---', 'ECO': 'j--', 'SPORT': '---'}, kinds ['base', 'hop', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:hop(B=2,preJ)->[ECO@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1, SPORT@1]; ECO:base(B=1); NORMAL:hop(B=1,postJ)->[ECO@1]; SPORT:hop(B=1,postJ)->[ECO@1]`
    * from `ECO`: `ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1, SPORT@1]; ECO:base(B=1); NORMAL:hop(B=1,postJ)->[ECO@1]; SPORT:hop(B=1,postJ)->[ECO@1]`
    * from `SPORT`: `SPORT:hop(B=2,preJ)->[ECO@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1, SPORT@1]; ECO:base(B=1); NORMAL:hop(B=1,postJ)->[ECO@1]; SPORT:hop(B=1,postJ)->[ECO@1]`
* cover `NORMAL_L`: λ = 6/5, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': '---', 'SPORT': '---'}, kinds ['base', 'hop', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `ECO`: `ECO:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `SPORT`: `SPORT:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
* cover `SPORT_L`: λ = 29/25, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': '---', 'ECO': '---', 'SPORT': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:hop(B=2,preJ)->[SPORT@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1, ECO@1]; SPORT:base(B=1); NORMAL:hop(B=1,postJ)->[SPORT@1]; ECO:hop(B=1,postJ)->[SPORT@1]`
    * from `ECO`: `ECO:hop(B=2,preJ)->[SPORT@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1, ECO@1]; SPORT:base(B=1); NORMAL:hop(B=1,postJ)->[SPORT@1]; ECO:hop(B=1,postJ)->[SPORT@1]`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1, ECO@1]; SPORT:base(B=1); NORMAL:hop(B=1,postJ)->[SPORT@1]; ECO:hop(B=1,postJ)->[SPORT@1]`
* cells: **M1** yes: ECO λ=5/4, NORMAL λ=6/5, SPORT λ=29/25 (affine dynamics); **M2** yes: ECO B=2 via ECO +choice NORMAL:hop/SPORT:hop, NORMAL B=2 via NORMAL +choice ECO:hop/SPORT:hop, SPORT B=2 via SPORT +choice ECO:hop/NORMAL:hop; **M3** yes: ECO branch=2, NORMAL branch=2, SPORT branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.ECO: 3 conjunct(s); L.NORMAL: 3 conjunct(s); L.SPORT: 3 conjunct(s); R.NORMAL: 3 conjunct(s); R.ECO: 3 conjunct(s); R.SPORT: 3 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rampmeter_poll_2to1`

* family: Freeway ramp metering (polled detectors); scenario: degraded-network; dims L/R 3/3; modes L/R 6/6; εL/εR 40/20; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8d8e73d122a0`
* `relcert`: **CERTIFIED** (2195 ms); `[prune] rampmeter_poll_2to1: [R1440->R1800]`; NO_PRUNE: **CERTIFIED** (2095 ms); NO_CUT: **CERTIFIED** (1883 ms); NO_IMPLIED_CUT: **CERTIFIED** (2072 ms); NO_LINEAR_CUT: **CERTIFIED** (2094 ms); domains: uniform
* `[cut] L.R1800: 3 conjunct(s)`
* `[cut] L.R1440: 5 conjunct(s)`
* `[cut] L.R1200: 4 conjunct(s)`
* `[cut] L.R960: 4 conjunct(s)`
* `[cut] L.R720: 5 conjunct(s)`
* `[cut] L.R480: 3 conjunct(s)`
* `[cut] R.R1800: 3 conjunct(s)`
* `[cut] R.R1440: 5 conjunct(s)`
* `[cut] R.R1200: 4 conjunct(s)`
* `[cut] R.R960: 4 conjunct(s)`
* `[cut] R.R720: 5 conjunct(s)`
* `[cut] R.R480: 3 conjunct(s)`
* `[cut-x] L.R720: k <= 39 kind=closure entry=weakening route=diB`
* `[cut-x] R.R720: k <= 39 kind=closure entry=weakening route=diB`
* `[admissible] R1800_L: [R1800, R1440, R1200]`
* `[admissible] R1440_L: [R1800, R1440, R1200, R960]`
* `[admissible] R1200_L: [R1800, R1440, R1200, R960, R720]`
* `[admissible] R960_L: [R1440, R1200, R960, R720, R480]`
* `[admissible] R720_L: [R1200, R960, R720, R480]`
* `[admissible] R480_L: [R960, R720, R480]`
* `--handoff`: 36/36 checked, 36 passed, failing -, VACUOUS (identical rows) (116 ms)
* cover `R1800_L`: λ = 1, budget 2, admissible ['R1800', 'R1440', 'R1200'], flags {'R1800': 'j--', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': '---', 'R480': '---'}, kinds ['base', 'joint'], path modes ['R1200', 'R1440', 'R1800', 'R960'], branching 2, right-only False
    * from `R1800`: `R1800:joint(B=2)->[R1800@1, R1800@1, R1440@1, R1200@1]; R1800:base(B=1); R1440:base(B=1); R1200:base(B=1)`
    * from `R1440`: `R1440:joint(B=2)->[R1440@1, R1440@1, R1200@1]; R1440:base(B=1); R1200:base(B=1)`
    * from `R1200`: `R1200:joint(B=2)->[R1200@1, R1440@1, R1200@1, R960@1]; R1200:base(B=1); R1440:base(B=1); R960:base(B=1)`
* cover `R1440_L`: λ = 1, budget 2, admissible ['R1800', 'R1440', 'R1200', 'R960'], flags {'R1800': 'j--', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': 'j--', 'R480': 'j--'}, kinds ['base', 'joint'], path modes ['R1200', 'R1440', 'R1800', 'R720', 'R960'], branching 2, right-only False
    * from `R1800`: `R1800:joint(B=2)->[R1800@1, R1800@1, R1440@1, R1200@1]; R1800:base(B=1); R1440:base(B=1); R1200:base(B=1)`
    * from `R1440`: `R1440:joint(B=2)->[R1440@1, R1440@1, R1200@1]; R1440:base(B=1); R1200:base(B=1)`
    * from `R1200`: `R1200:joint(B=2)->[R1200@1, R1440@1, R1200@1, R960@1]; R1200:base(B=1); R1440:base(B=1); R960:base(B=1)`
    * from `R960`: `R960:joint(B=2)->[R960@1, R1200@1, R960@1, R720@1]; R960:base(B=1); R1200:base(B=1); R720:base(B=1)`
* cover `R1200_L`: λ = 1, budget 2, admissible ['R1800', 'R1440', 'R1200', 'R960', 'R720'], flags {'R1800': 'j--', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': 'j--', 'R480': 'j--'}, kinds ['base', 'joint'], path modes ['R1200', 'R1440', 'R1800', 'R480', 'R720', 'R960'], branching 2, right-only False
    * from `R1800`: `R1800:joint(B=2)->[R1800@1, R1800@1, R1440@1, R1200@1]; R1800:base(B=1); R1440:base(B=1); R1200:base(B=1)`
    * from `R1440`: `R1440:joint(B=2)->[R1440@1, R1440@1, R1200@1]; R1440:base(B=1); R1200:base(B=1)`
    * from `R1200`: `R1200:joint(B=2)->[R1200@1, R1440@1, R1200@1, R960@1]; R1200:base(B=1); R1440:base(B=1); R960:base(B=1)`
    * from `R960`: `R960:joint(B=2)->[R960@1, R1200@1, R960@1, R720@1]; R960:base(B=1); R1200:base(B=1); R720:base(B=1)`
    * from `R720`: `R720:joint(B=2)->[R720@1, R960@1, R720@1, R480@1]; R720:base(B=1); R960:base(B=1); R480:base(B=1)`
* cover `R960_L`: λ = 1, budget 2, admissible ['R1440', 'R1200', 'R960', 'R720', 'R480'], flags {'R1800': 'j--', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': 'j--', 'R480': 'j--'}, kinds ['base', 'joint'], path modes ['R1200', 'R1440', 'R480', 'R720', 'R960'], branching 2, right-only False
    * from `R1440`: `R1440:joint(B=2)->[R1440@1, R1440@1, R1200@1]; R1440:base(B=1); R1200:base(B=1)`
    * from `R1200`: `R1200:joint(B=2)->[R1200@1, R1440@1, R1200@1, R960@1]; R1200:base(B=1); R1440:base(B=1); R960:base(B=1)`
    * from `R960`: `R960:joint(B=2)->[R960@1, R1200@1, R960@1, R720@1]; R960:base(B=1); R1200:base(B=1); R720:base(B=1)`
    * from `R720`: `R720:joint(B=2)->[R720@1, R960@1, R720@1, R480@1]; R720:base(B=1); R960:base(B=1); R480:base(B=1)`
    * from `R480`: `R480:joint(B=2)->[R480@1, R960@1, R720@1, R480@1]; R480:base(B=1); R960:base(B=1); R720:base(B=1)`
* cover `R720_L`: λ = 1, budget 2, admissible ['R1200', 'R960', 'R720', 'R480'], flags {'R1800': '---', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': 'j--', 'R480': 'j--'}, kinds ['base', 'joint'], path modes ['R1200', 'R1440', 'R480', 'R720', 'R960'], branching 2, right-only False
    * from `R1200`: `R1200:joint(B=2)->[R1200@1, R1440@1, R1200@1, R960@1]; R1200:base(B=1); R1440:base(B=1); R960:base(B=1)`
    * from `R960`: `R960:joint(B=2)->[R960@1, R1200@1, R960@1, R720@1]; R960:base(B=1); R1200:base(B=1); R720:base(B=1)`
    * from `R720`: `R720:joint(B=2)->[R720@1, R960@1, R720@1, R480@1]; R720:base(B=1); R960:base(B=1); R480:base(B=1)`
    * from `R480`: `R480:joint(B=2)->[R480@1, R960@1, R720@1, R480@1]; R480:base(B=1); R960:base(B=1); R720:base(B=1)`
* cover `R480_L`: λ = 1, budget 2, admissible ['R960', 'R720', 'R480'], flags {'R1800': '---', 'R1440': 'j--', 'R1200': 'j--', 'R960': 'j--', 'R720': 'j--', 'R480': 'j--'}, kinds ['base', 'joint'], path modes ['R1200', 'R480', 'R720', 'R960'], branching 2, right-only False
    * from `R960`: `R960:joint(B=2)->[R960@1, R1200@1, R960@1, R720@1]; R960:base(B=1); R1200:base(B=1); R720:base(B=1)`
    * from `R720`: `R720:joint(B=2)->[R720@1, R960@1, R720@1, R480@1]; R720:base(B=1); R960:base(B=1); R480:base(B=1)`
    * from `R480`: `R480:joint(B=2)->[R480@1, R960@1, R720@1, R480@1]; R480:base(B=1); R960:base(B=1); R720:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: R1800 B=2 via R1200/R1440/R1800, R1440 B=2 via R1200/R1440/R1800/R960, R1200 B=2 via R1200/R1440/R1800/R720/R960, R960 B=2 via R1200/R1440/R480/R720/R960, R720 B=2 via R1200/R480/R720/R960, R480 B=2 via R480/R720/R960; **M3** yes: R1800 branch=2, R1440 branch=2, R1200 branch=2, R960 branch=2, R720 branch=2, R480 branch=2; **M4** vacuous: pruned R1440->R1800 but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.R1800: 3 conjunct(s); L.R1440: 5 conjunct(s); L.R1200: 4 conjunct(s); L.R960: 4 conjunct(s); L.R720: 5 conjunct(s); L.R480: 3 conjunct(s); R.R1800: 3 conjunct(s); R.R1440: 5 conjunct(s); R.R1200: 4 conjunct(s); R.R960: 4 conjunct(s); R.R720: 5 conjunct(s); R.R480: 3 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.R720: k <= 39 kind=closure entry=weakening route=diB; R.R720: k <= 39 kind=closure entry=weakening route=diB) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `reactor_feed_wireless`

* family: Exothermic reactor feed interlock; scenario: degraded-sensor; dims L/R 2/2; modes L/R 4/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `c0f2eebc0b05`
* `relcert`: **CERTIFIED** (745 ms); `[prune] reactor_feed_wireless: [F1->F4, F2->F4, F3->F1, F4->F1]`; NO_PRUNE: **DECLINED** (326 ms); NO_CUT: **CERTIFIED** (713 ms); NO_IMPLIED_CUT: **CERTIFIED** (731 ms); NO_LINEAR_CUT: **CERTIFIED** (749 ms); domains: uniform
* `[cut] L.F1: 4 conjunct(s)`
* `[cut] L.F2: 4 conjunct(s)`
* `[cut] L.F3: 4 conjunct(s)`
* `[cut] L.F4: 4 conjunct(s)`
* `[cut] R.F1: 4 conjunct(s)`
* `[cut] R.F2: 4 conjunct(s)`
* `[cut] R.F3: 4 conjunct(s)`
* `[cut] R.F4: 4 conjunct(s)`
* `[admissible] F1_L: [F1, F2]`
* `[admissible] F2_L: [F1, F2, F3]`
* `[admissible] F3_L: [F2, F3, F4]`
* `[admissible] F4_L: [F3, F4]`
* `--handoff`: 16/16 checked, 16 passed, failing -, VACUOUS (identical rows) (117 ms)
* cover `F1_L`: λ = 1, budget 2, admissible ['F1', 'F2'], flags {'F1': 'j--', 'F2': 'j--', 'F3': 'j--', 'F4': '---'}, kinds ['base', 'joint'], path modes ['F1', 'F2', 'F3'], branching 2, right-only False
    * from `F1`: `F1:joint(B=2)->[F1@1, F1@1, F2@1, F3@1]; F1:base(B=1); F2:base(B=1); F3:base(B=1)`
    * from `F2`: `F2:joint(B=2)->[F2@1, F1@1, F2@1, F3@1]; F2:base(B=1); F1:base(B=1); F3:base(B=1)`
* cover `F2_L`: λ = 1, budget 2, admissible ['F1', 'F2', 'F3'], flags {'F1': 'j--', 'F2': 'j--', 'F3': 'j--', 'F4': 'j--'}, kinds ['base', 'joint'], path modes ['F1', 'F2', 'F3', 'F4'], branching 2, right-only False
    * from `F1`: `F1:joint(B=2)->[F1@1, F1@1, F2@1, F3@1]; F1:base(B=1); F2:base(B=1); F3:base(B=1)`
    * from `F2`: `F2:joint(B=2)->[F2@1, F1@1, F2@1, F3@1]; F2:base(B=1); F1:base(B=1); F3:base(B=1)`
    * from `F3`: `F3:joint(B=2)->[F3@1, F2@1, F3@1, F4@1]; F3:base(B=1); F2:base(B=1); F4:base(B=1)`
* cover `F3_L`: λ = 1, budget 2, admissible ['F2', 'F3', 'F4'], flags {'F1': 'j--', 'F2': 'j--', 'F3': 'j--', 'F4': 'j--'}, kinds ['base', 'joint'], path modes ['F1', 'F2', 'F3', 'F4'], branching 2, right-only False
    * from `F2`: `F2:joint(B=2)->[F2@1, F1@1, F2@1, F3@1]; F2:base(B=1); F1:base(B=1); F3:base(B=1)`
    * from `F3`: `F3:joint(B=2)->[F3@1, F2@1, F3@1, F4@1]; F3:base(B=1); F2:base(B=1); F4:base(B=1)`
    * from `F4`: `F4:joint(B=2)->[F4@1, F2@1, F3@1, F4@1]; F4:base(B=1); F2:base(B=1); F3:base(B=1)`
* cover `F4_L`: λ = 1, budget 2, admissible ['F3', 'F4'], flags {'F1': '---', 'F2': 'j--', 'F3': 'j--', 'F4': 'j--'}, kinds ['base', 'joint'], path modes ['F2', 'F3', 'F4'], branching 2, right-only False
    * from `F3`: `F3:joint(B=2)->[F3@1, F2@1, F3@1, F4@1]; F3:base(B=1); F2:base(B=1); F4:base(B=1)`
    * from `F4`: `F4:joint(B=2)->[F4@1, F2@1, F3@1, F4@1]; F4:base(B=1); F2:base(B=1); F3:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: F1 B=2 via F1/F2, F2 B=2 via F1/F2/F3, F3 B=2 via F2/F3/F4, F4 B=2 via F3/F4; **M3** yes: F1 branch=2, F2 branch=2, F3 branch=2, F4 branch=2; **M4** yes: pruned F1->F4, F2->F4, F3->F1, F4->F1; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.F1: 4 conjunct(s); L.F2: 4 conjunct(s); L.F3: 4 conjunct(s); L.F4: 4 conjunct(s); R.F1: 4 conjunct(s); R.F2: 4 conjunct(s); R.F3: 4 conjunct(s); R.F4: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_ladder_2to3`

* family: Rover ladder; scenario: model-refinement; dims L/R 3/3; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `f54a96a9b7cd`
* `relcert`: **CERTIFIED** (329 ms); `[prune] rover_ladder_2to3: []`; NO_PRUNE: **CERTIFIED** (309 ms); NO_CUT: **CERTIFIED** (216 ms); NO_IMPLIED_CUT: **CERTIFIED** (272 ms); NO_LINEAR_CUT: **CERTIFIED** (278 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (91 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_ladder_3to6`

* family: Rover ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `07858bde53e7`
* `relcert`: **CERTIFIED** (729 ms); `[prune] rover_ladder_3to6: []`; NO_PRUNE: **CERTIFIED** (792 ms); NO_CUT: **CERTIFIED** (687 ms); NO_IMPLIED_CUT: **CERTIFIED** (743 ms); NO_LINEAR_CUT: **CERTIFIED** (785 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (58 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_ladder_6to8`

* family: Rover ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.25]; invariant shape quadratic+conj; rows identical: True; normalized md5 `d3d269dc3dae`
* `relcert`: **CERTIFIED** (15026 ms); `[prune] rover_ladder_6to8: []`; NO_PRUNE: **CERTIFIED** (15252 ms); NO_CUT: **DECLINED** (12982 ms); NO_IMPLIED_CUT: **CERTIFIED** (15109 ms); NO_LINEAR_CUT: **CERTIFIED** (15219 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (20 ms)
* cover `STEEP_L`: λ = 11/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 11/10, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER'], branching 1, right-only False
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 11/10, budget 2, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT B=2 via FLAT; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_ladder_8to12`

* family: Rover ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.25]; invariant shape quadratic+conj; rows identical: True; normalized md5 `8aba42cd8980`
* `relcert`: **CERTIFIED** (31424 ms); `[prune] rover_ladder_8to12: []`; NO_PRUNE: **CERTIFIED** (31548 ms); NO_CUT: **DECLINED** (31901 ms); NO_IMPLIED_CUT: **CERTIFIED** (31384 ms); NO_LINEAR_CUT: **CERTIFIED** (31487 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (105 ms)
* cover `STEEP_L`: λ = 11/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 11/10, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER'], branching 1, right-only False
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 11/10, budget 2, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base', 'joint'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT B=2 via FLAT; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_patrol_lag`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 4/4; εL/εR 1.0/1.0; λ ∈ [1.0, 1.5]; invariant shape conjunctive; rows identical: True; normalized md5 `b091be388a32`
* `relcert`: **CERTIFIED** (1279 ms); `[prune] rover_patrol_lag: []`; NO_PRUNE: **CERTIFIED** (1268 ms); NO_CUT: **CERTIFIED** (1618 ms); NO_IMPLIED_CUT: **CERTIFIED** (1240 ms); NO_LINEAR_CUT: **CERTIFIED** (1264 ms); domains: uniform
* `[cut] L.SLOW: 1 conjunct(s)`
* `[cut] L.MEDIUM_ECO: 1 conjunct(s)`
* `[cut] L.MEDIUM_BRISK: 1 conjunct(s)`
* `[cut] L.FAST: 1 conjunct(s)`
* `[cut] R.SLOW: 1 conjunct(s)`
* `[cut] R.MEDIUM_ECO: 1 conjunct(s)`
* `[cut] R.MEDIUM_BRISK: 1 conjunct(s)`
* `[cut] R.FAST: 1 conjunct(s)`
* `[admissible] SLOW_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_ECO_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_BRISK_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] FAST_L: [MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `--handoff`: 10/10 checked, 10 passed, failing -, VACUOUS (identical rows) (103 ms)
* cover `SLOW_L`: λ = 1, budget 1, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': 'jdd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'j--'}, kinds ['base'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 0, right-only False
    * from `SLOW`: `SLOW:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:base(B=1)`
    * from `FAST`: `FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 1, budget 1, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'j--'}, kinds ['base', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 0, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=1,preJ)->[MEDIUM_ECO@1, MEDIUM_BRISK@1]; MEDIUM_ECO:base(B=1); MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:base(B=1)`
    * from `FAST`: `FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 1, budget 1, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'j--'}, kinds ['base', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 0, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=1,preJ)->[MEDIUM_ECO@1, MEDIUM_BRISK@1]; MEDIUM_ECO:repoDyn(B=1,preJ)->[MEDIUM_BRISK@1, FAST@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=1,preJ)->[MEDIUM_BRISK@1, FAST@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:base(B=1)`
    * from `FAST`: `FAST:base(B=1)`
* cover `FAST_L`: λ = 11/8, budget 2, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 2, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=2,preJ)->[MEDIUM_BRISK@2, FAST@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, MEDIUM_BRISK@1, MEDIUM_ECO@1, FAST@1]; MEDIUM_BRISK:base(B=1); MEDIUM_ECO:repoDyn(B=1,postJ)->[MEDIUM_BRISK@1, FAST@1]; FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, MEDIUM_BRISK@1, MEDIUM_ECO@1, FAST@1]; MEDIUM_BRISK:base(B=1); MEDIUM_ECO:repoDyn(B=1,postJ)->[MEDIUM_BRISK@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** yes: FAST λ=11/8 (affine dynamics); **M2** yes: FAST B=2 via FAST/MEDIUM_BRISK +RO; **M3** yes: FAST branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.SLOW: 1 conjunct(s); L.MEDIUM_ECO: 1 conjunct(s); L.MEDIUM_BRISK: 1 conjunct(s); L.FAST: 1 conjunct(s); R.SLOW: 1 conjunct(s); R.MEDIUM_ECO: 1 conjunct(s); R.MEDIUM_BRISK: 1 conjunct(s); R.FAST: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_terrain_2to4`

* family: Terrain chain; scenario: model-refinement; dims L/R 4/4; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `897f37a4d177`
* `relcert`: **CERTIFIED** (588 ms); `[prune] rover_terrain_2to4: []`; NO_PRUNE: **CERTIFIED** (580 ms); NO_CUT: **DECLINED** (259 ms); NO_IMPLIED_CUT: **CERTIFIED** (505 ms); NO_LINEAR_CUT: **CERTIFIED** (601 ms); domains: uniform
* `[cut] L.MUD: 2 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 1 conjunct(s)`
* `[cut] R.GRAVEL: 1 conjunct(s)`
* `[cut] R.PAVED: 1 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (78 ms)
* cover `MUD_L`: λ = 1, budget 1, admissible ['MUD', 'GRAVEL', 'PAVED'], flags {'MUD': 'j--', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'MUD', 'PAVED'], branching 0, right-only False
    * from `MUD`: `MUD:base(B=1)`
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `GRAVEL_L`: λ = 1, budget 1, admissible ['GRAVEL', 'PAVED'], flags {'MUD': '---', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'PAVED'], branching 0, right-only False
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `PAVED_L`: λ = 1, budget 1, admissible ['PAVED'], flags {'MUD': '---', 'GRAVEL': '---', 'PAVED': 'j--'}, kinds ['base'], path modes ['PAVED'], branching 0, right-only False
    * from `PAVED`: `PAVED:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conjunct(s); R.MUD: 1 conjunct(s); R.GRAVEL: 1 conjunct(s); R.PAVED: 1 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_terrain_4to6`

* family: Terrain chain; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `4993659832a9`
* `relcert`: **CERTIFIED** (1103 ms); `[prune] rover_terrain_4to6: []`; NO_PRUNE: **CERTIFIED** (1089 ms); NO_CUT: **DECLINED** (463 ms); NO_IMPLIED_CUT: **CERTIFIED** (1014 ms); NO_LINEAR_CUT: **CERTIFIED** (1106 ms); domains: uniform
* `[cut] L.MUD: 2 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 2 conjunct(s)`
* `[cut] R.GRAVEL: 2 conjunct(s)`
* `[cut] R.PAVED: 2 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `MUD_L`: λ = 1, budget 1, admissible ['MUD', 'GRAVEL', 'PAVED'], flags {'MUD': 'j--', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'MUD', 'PAVED'], branching 0, right-only False
    * from `MUD`: `MUD:base(B=1)`
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `GRAVEL_L`: λ = 1, budget 1, admissible ['GRAVEL', 'PAVED'], flags {'MUD': '---', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'PAVED'], branching 0, right-only False
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `PAVED_L`: λ = 1, budget 1, admissible ['PAVED'], flags {'MUD': '---', 'GRAVEL': '---', 'PAVED': 'j--'}, kinds ['base'], path modes ['PAVED'], branching 0, right-only False
    * from `PAVED`: `PAVED:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conjunct(s); R.MUD: 2 conjunct(s); R.GRAVEL: 2 conjunct(s); R.PAVED: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_terrain_6to12`

* family: Terrain chain; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `2e1c6c226285`
* `relcert`: **CERTIFIED** (1792 ms); `[prune] rover_terrain_6to12: []`; NO_PRUNE: **CERTIFIED** (1780 ms); NO_CUT: **DECLINED** (613 ms); NO_IMPLIED_CUT: **CERTIFIED** (1736 ms); NO_LINEAR_CUT: **CERTIFIED** (1790 ms); domains: uniform
* `[cut] L.MUD: 3 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 2 conjunct(s)`
* `[cut] R.GRAVEL: 2 conjunct(s)`
* `[cut] R.PAVED: 2 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (89 ms)
* cover `MUD_L`: λ = 1, budget 1, admissible ['MUD', 'GRAVEL', 'PAVED'], flags {'MUD': 'j--', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'MUD', 'PAVED'], branching 0, right-only False
    * from `MUD`: `MUD:base(B=1)`
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `GRAVEL_L`: λ = 1, budget 1, admissible ['GRAVEL', 'PAVED'], flags {'MUD': '---', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'PAVED'], branching 0, right-only False
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `PAVED_L`: λ = 1, budget 1, admissible ['PAVED'], flags {'MUD': '---', 'GRAVEL': '---', 'PAVED': 'j--'}, kinds ['base'], path modes ['PAVED'], branching 0, right-only False
    * from `PAVED`: `PAVED:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.MUD: 3 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conjunct(s); R.MUD: 2 conjunct(s); R.GRAVEL: 2 conjunct(s); R.PAVED: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `sat3w_detumble_phases`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 6/6; modes L/R 2/3; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `bafd3c6db077`
* `relcert`: **CERTIFIED** (20261 ms); `[prune] sat3w_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **CERTIFIED** (20285 ms); NO_CUT: **DECLINED** (6808 ms); NO_IMPLIED_CUT: **CERTIFIED** (20233 ms); NO_LINEAR_CUT: **CERTIFIED** (20282 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.FINE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE, FINE]`
* `[admissible] FINE_L: [DETUMBLE, FINE]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (108 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': 'j--', 'FINE': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
    * from `FINE`: `FINE:hop(B=2,preJ)->[DETUMBLE@2]; DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': '---', 'FINE': 'j--', 'SAFE': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:hop(B=2,preJ)->[FINE@2]; FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
    * from `FINE`: `FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE +choice DETUMBLE:hop; **M3** no (max non-self successors at a joint step = 1); **M4** vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.FINE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_phases`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 4/4; modes L/R 2/3; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `3dfdebee5dd4`
* `relcert`: **CERTIFIED** (7135 ms); `[prune] sat_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **CERTIFIED** (7167 ms); NO_CUT: **DECLINED** (3649 ms); NO_IMPLIED_CUT: **CERTIFIED** (7189 ms); NO_LINEAR_CUT: **CERTIFIED** (7215 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.FINE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE, FINE]`
* `[admissible] FINE_L: [DETUMBLE, FINE]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (101 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': 'j--', 'FINE': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
    * from `FINE`: `FINE:hop(B=2,preJ)->[DETUMBLE@2]; DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': '---', 'FINE': 'j--', 'SAFE': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:hop(B=2,preJ)->[FINE@2]; FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
    * from `FINE`: `FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE +choice DETUMBLE:hop; **M3** no (max non-self successors at a joint step = 1); **M4** vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.FINE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_weak`

* family: Rigid-body detumbling (polynomial); scenario: degraded-actuator; dims L/R 4/4; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [0.8, 0.8]; invariant shape quadratic; rows identical: True; normalized md5 `8a34e7734d56`
* `relcert`: **CERTIFIED** (4068 ms); `[prune] sat_detumble_weak: [NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE]`; NO_PRUNE: **CERTIFIED** (4047 ms); NO_CUT: **CERTIFIED** (3990 ms); NO_IMPLIED_CUT: **CERTIFIED** (4052 ms); NO_LINEAR_CUT: **CERTIFIED** (4060 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.NOMINAL: 1 conjunct(s)`
* `[cut] R.ECONOMY: 1 conjunct(s)`
* `[cut] R.SURVIVAL: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [NOMINAL, ECONOMY, SURVIVAL]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (1073 ms)
* cover `DETUMBLE_L`: λ = 4/5, budget 2, admissible ['NOMINAL', 'ECONOMY', 'SURVIVAL'], flags {'NOMINAL': 'j--', 'ECONOMY': '---', 'SURVIVAL': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['ECONOMY', 'NOMINAL', 'SURVIVAL'], branching 2, right-only False
    * from `NOMINAL`: `NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
    * from `ECONOMY`: `ECONOMY:hop(B=2,preJ)->[NOMINAL@2]; NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
    * from `SURVIVAL`: `SURVIVAL:hop(B=2,preJ)->[NOMINAL@2]; NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
* cells: **M1** yes: DETUMBLE λ=4/5 (polynomial dynamics); **M2** yes: DETUMBLE B=2 via NOMINAL +choice ECONOMY:hop/SURVIVAL:hop; **M3** yes: DETUMBLE branch=2; **M4** vacuous: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY: 1 conjunct(s); R.SURVIVAL: 1 conjunct(s); R.SAFE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `syringe_relay_prearm`

* family: Syringe-pump relay; scenario: controller-change; dims L/R 4/4; modes L/R 6/4; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `1d16789caafc`
* `relcert`: **CERTIFIED** (1104 ms); `[prune] syringe_relay_prearm: []`; NO_PRUNE: **CERTIFIED** (1097 ms); NO_CUT: **CERTIFIED** (1130 ms); NO_IMPLIED_CUT: **CERTIFIED** (1063 ms); NO_LINEAR_CUT: **CERTIFIED** (1111 ms); domains: uniform
* `[cut] L.RUN1: 8 conjunct(s)`
* `[cut] L.PREARM: 8 conjunct(s)`
* `[cut] L.TAKEUP2: 8 conjunct(s)`
* `[cut] L.RUN2: 9 conjunct(s)`
* `[cut] L.END: 9 conjunct(s)`
* `[cut] R.RUN1: 8 conjunct(s)`
* `[cut] R.TAKEUP2: 8 conjunct(s)`
* `[cut] R.RUN2: 9 conjunct(s)`
* `[cut] R.END: 9 conjunct(s)`
* `[admissible] RUN1_L: [RUN1]`
* `[admissible] PREARM_L: [RUN1]`
* `[admissible] READY_L: [RUN1]`
* `[admissible] TAKEUP2_L: [TAKEUP2]`
* `[admissible] RUN2_L: [TAKEUP2, RUN2]`
* `[admissible] END_L: [END]`
* `--handoff`: 13/13 checked, 13 passed, failing -, non-vacuous (300 ms)
* cover `RUN1_L`: λ = 1, budget 1, admissible ['RUN1'], flags {'RUN1': 'j--', 'TAKEUP2': '-d-', 'RUN2': '-d-', 'END': 'j--'}, kinds ['base'], path modes ['RUN1'], branching 0, right-only False
    * from `RUN1`: `RUN1:base(B=1)`
* cover `PREARM_L`: λ = 1, budget 1, admissible ['RUN1'], flags {'RUN1': 'j--', 'TAKEUP2': '-d-', 'RUN2': '-d-', 'END': 'j--'}, kinds ['base'], path modes ['RUN1'], branching 0, right-only False
    * from `RUN1`: `RUN1:base(B=1)`
* cover `READY_L`: λ = 1, budget 1, admissible ['RUN1'], flags {'RUN1': 'j--', 'TAKEUP2': '-d-', 'RUN2': '-d-', 'END': 'j--'}, kinds ['base'], path modes ['RUN1'], branching 0, right-only False
    * from `RUN1`: `RUN1:base(B=1)`
* cover `TAKEUP2_L`: λ = 1, budget 1, admissible ['TAKEUP2'], flags {'RUN1': '---', 'TAKEUP2': 'j--', 'RUN2': '-d-', 'END': 'j--'}, kinds ['base'], path modes ['TAKEUP2'], branching 0, right-only False
    * from `TAKEUP2`: `TAKEUP2:base(B=1)`
* cover `RUN2_L`: λ = 1, budget 1, admissible ['TAKEUP2', 'RUN2'], flags {'RUN1': '---', 'TAKEUP2': '-dd', 'RUN2': 'j--', 'END': '---'}, kinds ['base', 'repoDyn'], path modes ['RUN2', 'TAKEUP2'], branching 0, right-only True
    * from `TAKEUP2`: `TAKEUP2:repoDyn(B=1,preJ)->[RUN2@1]; RUN2:base(B=1)`
    * from `RUN2`: `RUN2:base(B=1)`
* cover `END_L`: λ = 1, budget 1, admissible ['END'], flags {'RUN1': 'jdd', 'TAKEUP2': 'jdd', 'RUN2': '---', 'END': 'j--'}, kinds ['base'], path modes ['END'], branching 0, right-only False
    * from `END`: `END:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 13/13 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.RUN1: 8 conjunct(s); L.PREARM: 8 conjunct(s); L.TAKEUP2: 8 conjunct(s); L.RUN2: 9 conjunct(s); L.END: 9 conjunct(s); R.RUN1: 8 conjunct(s); R.TAKEUP2: 8 conjunct(s); R.RUN2: 9 conjunct(s); R.END: 9 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `tank_dos_3to1`

* family: Tank under sampling DoS; scenario: dos-attack; dims L/R 2/2; modes L/R 4/4; εL/εR 30.0/10.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a4db20254b3a`
* `relcert`: **CERTIFIED** (878 ms); `[prune] tank_dos_3to1: []`; NO_PRUNE: **CERTIFIED** (947 ms); NO_CUT: **DECLINED** (277 ms); NO_IMPLIED_CUT: **CERTIFIED** (876 ms); NO_LINEAR_CUT: **CERTIFIED** (868 ms); domains: uniform
* `[cut] L.P2: 4 conjunct(s)`
* `[cut] L.P3: 3 conjunct(s)`
* `[cut] L.P4: 3 conjunct(s)`
* `[cut] L.P5: 3 conjunct(s)`
* `[cut] R.P2: 4 conjunct(s)`
* `[cut] R.P3: 3 conjunct(s)`
* `[cut] R.P4: 3 conjunct(s)`
* `[cut] R.P5: 3 conjunct(s)`
* `[cut-x] L.P2: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.P3: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.P4: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.P2: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.P3: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.P4: w <= 22.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] P2_L: [P2]`
* `[admissible] P3_L: [P3]`
* `[admissible] P4_L: [P4]`
* `[admissible] P5_L: [P5]`
* `--handoff`: 10/10 checked, 10 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `P2_L`: λ = 1, budget 3, admissible ['P2'], flags {'P2': 'j--', 'P3': 'j--', 'P4': 'j--', 'P5': '---'}, kinds ['base', 'joint'], path modes ['P2', 'P3', 'P4'], branching 1, right-only False
    * from `P2`: `P2:joint(B=3)->[P2@2, P2@2, P3@2]; P2:joint(B=2)->[P2@1, P2@1, P3@1]; P2:base(B=1); P3:base(B=1); P3:joint(B=2)->[P3@1, P3@1, P4@1]; P4:base(B=1)`
* cover `P3_L`: λ = 1, budget 3, admissible ['P3'], flags {'P2': '---', 'P3': 'j--', 'P4': 'j--', 'P5': 'j--'}, kinds ['base', 'joint'], path modes ['P3', 'P4', 'P5'], branching 1, right-only False
    * from `P3`: `P3:joint(B=3)->[P3@2, P3@2, P4@2]; P3:joint(B=2)->[P3@1, P3@1, P4@1]; P3:base(B=1); P4:base(B=1); P4:joint(B=2)->[P4@1, P4@1, P5@1]; P5:base(B=1)`
* cover `P4_L`: λ = 1, budget 3, admissible ['P4'], flags {'P2': '---', 'P3': '---', 'P4': 'j--', 'P5': 'j--'}, kinds ['base', 'joint'], path modes ['P4', 'P5'], branching 1, right-only False
    * from `P4`: `P4:joint(B=3)->[P4@2, P4@2, P5@2]; P4:joint(B=2)->[P4@1, P4@1, P5@1]; P4:base(B=1); P5:base(B=1); P5:joint(B=2)->[P5@1, P5@1]`
* cover `P5_L`: λ = 1, budget 3, admissible ['P5'], flags {'P2': '---', 'P3': '---', 'P4': '---', 'P5': 'j--'}, kinds ['base', 'joint'], path modes ['P5'], branching 0, right-only False
    * from `P5`: `P5:joint(B=3)->[P5@2, P5@2]; P5:joint(B=2)->[P5@1, P5@1]; P5:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: P2 B=3 via P2/P3, P3 B=3 via P3/P4, P4 B=3 via P4/P5, P5 B=3 via P5; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.P2: 4 conjunct(s); L.P3: 3 conjunct(s); L.P4: 3 conjunct(s); L.P5: 3 conjunct(s); R.P2: 4 conjunct(s); R.P3: 3 conjunct(s); R.P4: 3 conjunct(s); R.P5: 3 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.P2: w <= 22.0 kind=implied-contraction entry=rational route=shape; L.P3: w <= 22.0 kind=implied-contraction entry=rational route=shape; L.P4: w <= 22.0 kind=implied-contraction entry=rational route=shape; R.P2: w <= 22.0 kind=implied-contraction entry=rational route=shape; R.P3: w <= 22.0 kind=implied-contraction entry=rational route=shape; R.P4: w <= 22.0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `train_ato_odometry`

* family: Train speed control (ATO); scenario: degraded-sensor; dims L/R 1/1; modes L/R 3/3; εL/εR 0.5/0.5; λ ∈ [0.75, 1.25]; invariant shape conjunctive; rows identical: True; normalized md5 `07495914d776`
* `relcert`: **CERTIFIED** (2194 ms); `[prune] train_ato_odometry: []`; NO_PRUNE: **CERTIFIED** (2263 ms); NO_CUT: **CERTIFIED** (2219 ms); NO_IMPLIED_CUT: **CERTIFIED** (2255 ms); NO_LINEAR_CUT: **CERTIFIED** (2201 ms); domains: uniform
* `[cut] L.PL1: 2 conjunct(s)`
* `[cut] L.PL2: 2 conjunct(s)`
* `[cut] L.PL3: 2 conjunct(s)`
* `[cut] R.PL1: 2 conjunct(s)`
* `[cut] R.PL2: 2 conjunct(s)`
* `[cut] R.PL3: 2 conjunct(s)`
* `[admissible] PL1_L: [PL1, PL2, PL3]`
* `[admissible] PL2_L: [PL1, PL2, PL3]`
* `[admissible] PL3_L: [PL1, PL2, PL3]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (96 ms)
* cover `PL1_L`: λ = 6/5, budget 2, admissible ['PL1', 'PL2', 'PL3'], flags {'PL1': 'j--', 'PL2': 'j--', 'PL3': 'j--'}, kinds ['base', 'joint'], path modes ['PL1', 'PL2', 'PL3'], branching 2, right-only False
    * from `PL1`: `PL1:joint(B=2)->[PL1@1, PL1@1, PL2@1, PL3@1]; PL1:base(B=1); PL2:base(B=1); PL3:base(B=1)`
    * from `PL2`: `PL2:joint(B=2)->[PL2@1, PL1@1, PL2@1, PL3@1]; PL2:base(B=1); PL1:base(B=1); PL3:base(B=1)`
    * from `PL3`: `PL3:joint(B=2)->[PL3@1, PL1@1, PL2@1, PL3@1]; PL3:base(B=1); PL1:base(B=1); PL2:base(B=1)`
* cover `PL2_L`: λ = 11/10, budget 2, admissible ['PL1', 'PL2', 'PL3'], flags {'PL1': 'j--', 'PL2': 'j--', 'PL3': 'j--'}, kinds ['base', 'joint'], path modes ['PL1', 'PL2', 'PL3'], branching 2, right-only False
    * from `PL1`: `PL1:joint(B=2)->[PL1@1, PL1@1, PL2@1, PL3@1]; PL1:base(B=1); PL2:base(B=1); PL3:base(B=1)`
    * from `PL2`: `PL2:joint(B=2)->[PL2@1, PL1@1, PL2@1, PL3@1]; PL2:base(B=1); PL1:base(B=1); PL3:base(B=1)`
    * from `PL3`: `PL3:joint(B=2)->[PL3@1, PL1@1, PL2@1, PL3@1]; PL3:base(B=1); PL1:base(B=1); PL2:base(B=1)`
* cover `PL3_L`: λ = 39/40, budget 1, admissible ['PL1', 'PL2', 'PL3'], flags {'PL1': 'j--', 'PL2': 'j--', 'PL3': 'j--'}, kinds ['base'], path modes ['PL1', 'PL2', 'PL3'], branching 0, right-only False
    * from `PL1`: `PL1:base(B=1)`
    * from `PL2`: `PL2:base(B=1)`
    * from `PL3`: `PL3:base(B=1)`
* cells: **M1** yes: PL1 λ=6/5 (per pairing: {'PL1': '39/40', 'PL2': '43/40'}), PL2 λ=11/10 (per pairing: {'PL1': '7/8', 'PL2': '39/40'}), PL3 λ=39/40 (per pairing: {'PL1': '31/40', 'PL2': '7/8'}) (affine dynamics); **M2** yes: PL1 B=2 via PL1/PL2/PL3, PL2 B=2 via PL1/PL2/PL3; **M3** yes: PL1 branch=2, PL2 branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.PL1: 2 conjunct(s); L.PL2: 2 conjunct(s); L.PL3: 2 conjunct(s); R.PL1: 2 conjunct(s); R.PL2: 2 conjunct(s); R.PL3: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `turbine_startup_gearratio`

* family: Wind turbine start-up; scenario: degraded-controller (configuration error after a gearbox exchange); dims L/R 1/1; modes L/R 4/4; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `2cdf1fc8b5e1`
* `relcert`: **CERTIFIED** (474 ms); `[prune] turbine_startup_gearratio: [SPINUP->STOP, RAMP->STOP]`; NO_PRUNE: **DECLINED** (236 ms); NO_CUT: **DECLINED** (183 ms); NO_IMPLIED_CUT: **DECLINED** (184 ms); NO_LINEAR_CUT: **CERTIFIED** (498 ms); domains: uniform
* `[cut] L.SPINUP: 2 conjunct(s)`
* `[cut] L.RAMP: 2 conjunct(s)`
* `[cut] L.GEN: 1 conjunct(s)`
* `[cut] L.STOP: 1 conjunct(s)`
* `[cut] R.SPINUP: 2 conjunct(s)`
* `[cut] R.RAMP: 2 conjunct(s)`
* `[cut] R.GEN: 1 conjunct(s)`
* `[cut] R.STOP: 1 conjunct(s)`
* `[cut-x] L.SPINUP: w <= 9 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.RAMP: w <= 7.875 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STOP: w <= 2.1 kind=closure entry=weakening route=diB`
* `[cut-x] R.SPINUP: w <= 9 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.RAMP: w <= 7.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STOP: w <= 2.0 kind=closure entry=weakening route=diB`
* `[admissible] SPINUP_L: [SPINUP, RAMP, GEN]`
* `[admissible] RAMP_L: [RAMP, GEN]`
* `[admissible] GEN_L: [GEN]`
* `[admissible] STOP_L: [SPINUP, RAMP, GEN, STOP]`
* `--handoff`: 8/8 checked, 8 passed, failing -, VACUOUS (identical rows) (39 ms)
* cover `SPINUP_L`: λ = 1, budget 1, admissible ['SPINUP', 'RAMP', 'GEN'], flags {'SPINUP': 'jdd', 'RAMP': '-dd', 'GEN': 'j--', 'STOP': '---'}, kinds ['base', 'repoDyn'], path modes ['GEN', 'RAMP', 'SPINUP'], branching 0, right-only True
    * from `SPINUP`: `SPINUP:base(B=1)`
    * from `RAMP`: `RAMP:repoDyn(B=1,preJ)->[GEN@1]; GEN:base(B=1)`
    * from `GEN`: `GEN:base(B=1)`
* cover `RAMP_L`: λ = 1, budget 1, admissible ['RAMP', 'GEN'], flags {'SPINUP': 'jdd', 'RAMP': 'jdd', 'GEN': 'j--', 'STOP': 'j--'}, kinds ['base'], path modes ['GEN', 'RAMP'], branching 0, right-only False
    * from `RAMP`: `RAMP:base(B=1)`
    * from `GEN`: `GEN:base(B=1)`
* cover `GEN_L`: λ = 1, budget 1, admissible ['GEN'], flags {'SPINUP': '-dd', 'RAMP': '-dd', 'GEN': 'j--', 'STOP': 'j--'}, kinds ['base'], path modes ['GEN'], branching 0, right-only False
    * from `GEN`: `GEN:base(B=1)`
* cover `STOP_L`: λ = 1, budget 1, admissible ['SPINUP', 'RAMP', 'GEN', 'STOP'], flags {'SPINUP': 'jdd', 'RAMP': 'jdd', 'GEN': 'j--', 'STOP': 'j--'}, kinds ['base'], path modes ['GEN', 'RAMP', 'SPINUP', 'STOP'], branching 0, right-only False
    * from `SPINUP`: `SPINUP:base(B=1)`
    * from `RAMP`: `RAMP:base(B=1)`
    * from `GEN`: `GEN:base(B=1)`
    * from `STOP`: `STOP:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned SPINUP->STOP, RAMP->STOP; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.SPINUP: 2 conjunct(s); L.RAMP: 2 conjunct(s); L.GEN: 1 conjunct(s); L.STOP: 1 conjunct(s); R.SPINUP: 2 conjunct(s); R.RAMP: 2 conjunct(s); R.GEN: 1 conjunct(s); R.STOP: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.SPINUP: w <= 9 kind=implied-contraction entry=rational route=shape; L.RAMP: w <= 7.875 kind=implied-contraction entry=rational route=shape; L.STOP: w <= 2.1 kind=closure entry=weakening route=diB; R.SPINUP: w <= 9 kind=implied-contraction entry=rational route=shape; R.RAMP: w <= 7.5 kind=implied-contraction entry=rational route=shape; R.STOP: w <= 2.0 kind=closure entry=weakening route=diB; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `ventilator_vc_cuffleak`

* family: Volume-controlled ventilation; scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.01/0.01; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `baa2f505f1c9`
* `relcert`: **CERTIFIED** (253 ms); `[prune] ventilator_vc_cuffleak: []`; NO_PRUNE: **CERTIFIED** (310 ms); NO_CUT: **DECLINED** (296 ms); NO_IMPLIED_CUT: **DECLINED** (299 ms); NO_LINEAR_CUT: **CERTIFIED** (299 ms); domains: uniform
* `[cut] L.INSP: 1 conjunct(s)`
* `[cut] L.EXP: 3 conjunct(s)`
* `[cut] R.INSP: 1 conjunct(s)`
* `[cut] R.EXP: 3 conjunct(s)`
* `[cut-x] L.EXP: s <= 0.01 kind=closure entry=weakening route=frozen`
* `[cut-x] R.EXP: s <= 0.01 kind=closure entry=weakening route=frozen`
* `[admissible] INSP_L: [INSP]`
* `[admissible] EXP_L: [EXP]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (52 ms)
* cover `INSP_L`: λ = 1, budget 1, admissible ['INSP'], flags {'INSP': 'j--', 'EXP': '---'}, kinds ['base'], path modes ['INSP'], branching 0, right-only False
    * from `INSP`: `INSP:base(B=1)`
* cover `EXP_L`: λ = 1, budget 1, admissible ['EXP'], flags {'INSP': '---', 'EXP': 'j--'}, kinds ['base'], path modes ['EXP'], branching 0, right-only False
    * from `EXP`: `EXP:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.INSP: 1 conjunct(s); L.EXP: 3 conjunct(s); R.INSP: 1 conjunct(s); R.EXP: 3 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.EXP: s <= 0.01 kind=closure entry=weakening route=frozen; R.EXP: s <= 0.01 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `watertank`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/5; εL/εR 1.0/1.0; λ ∈ [1.0, 2.0]; invariant shape conjunctive; rows identical: True; normalized md5 `c07b468bdb88`
* `relcert`: **CERTIFIED** (2079 ms); `[prune] watertank: [Low->PumpOff]`; NO_PRUNE: **CERTIFIED** (2111 ms); NO_CUT: **CERTIFIED** (2386 ms); NO_IMPLIED_CUT: **CERTIFIED** (2554 ms); NO_LINEAR_CUT: **CERTIFIED** (2027 ms); domains: uniform
* `[cut] L.Low: 2 conjunct(s)`
* `[cut] L.Mid: 2 conjunct(s)`
* `[cut] L.High: 1 conjunct(s)`
* `[cut] R.Low: 2 conjunct(s)`
* `[cut] R.MidEco: 2 conjunct(s)`
* `[cut] R.MidBoost: 2 conjunct(s)`
* `[cut] R.High: 1 conjunct(s)`
* `[cut] R.PumpOff: 1 conjunct(s)`
* `[cut-x] L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.Mid: x <= 20.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.Low: x <= 12.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen`
* `[admissible] Low_L: [Low, MidEco, MidBoost]`
* `[admissible] Mid_L: [MidEco, MidBoost, High]`
* `[admissible] High_L: [High]`
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (453 ms)
* cover `Low_L`: λ = 2, budget 2, admissible ['Low', 'MidEco', 'MidBoost'], flags {'Low': 'j--', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'jd-', 'PumpOff': '---'}, kinds ['base', 'joint'], path modes ['High', 'Low', 'MidBoost', 'MidEco'], branching 2, right-only False
    * from `Low`: `Low:joint(B=2)->[Low@1, Low@1, MidEco@1, MidBoost@1]; Low:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
* cover `Mid_L`: λ = 2, budget 2, admissible ['MidEco', 'MidBoost', 'High'], flags {'Low': '---', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'j--', 'PumpOff': 'j--'}, kinds ['base', 'joint'], path modes ['High', 'MidBoost', 'MidEco'], branching 2, right-only False
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
    * from `High`: `High:joint(B=2)->[High@1, High@1, MidEco@1, MidBoost@1]; High:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
* cover `High_L`: λ = 1, budget 1, admissible ['High'], flags {'Low': 'jdd', 'MidEco': 'jdd', 'MidBoost': 'jdd', 'High': 'j--', 'PumpOff': 'j--'}, kinds ['base'], path modes ['High'], branching 0, right-only False
    * from `High`: `High:base(B=1)`
* cells: **M1** yes: Low λ=2, Mid λ=2 (affine dynamics); **M2** yes: Low B=2 via Low/MidBoost/MidEco, Mid B=2 via High/MidBoost/MidEco; **M3** yes: Low branch=2, Mid branch=2; **M4** vacuous: pruned Low->PumpOff but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.High: 1 conjunct(s); R.Low: 2 conjunct(s); R.MidEco: 2 conjunct(s); R.MidBoost: 2 conjunct(s); R.High: 1 conjunct(s); R.PumpOff: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape; L.Mid: x <= 20.0 kind=closure entry=weakening route=shape; R.Low: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape; R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape; R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `watertank_twospeed`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/6; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `906b84dd5e01`
* `relcert`: **CERTIFIED** (1864 ms); `[prune] watertank_twospeed: []`; NO_PRUNE: **CERTIFIED** (1874 ms); NO_CUT: **CERTIFIED** (2769 ms); NO_IMPLIED_CUT: **CERTIFIED** (3088 ms); NO_LINEAR_CUT: **CERTIFIED** (1872 ms); domains: uniform
* `[cut] L.Low: 2 conjunct(s)`
* `[cut] L.Mid: 2 conjunct(s)`
* `[cut] L.High: 1 conjunct(s)`
* `[cut] R.Fast: 2 conjunct(s)`
* `[cut] R.Slow: 2 conjunct(s)`
* `[cut] R.MidEco: 2 conjunct(s)`
* `[cut] R.MidBoost: 2 conjunct(s)`
* `[cut] R.High: 1 conjunct(s)`
* `[cut] R.PumpOff: 1 conjunct(s)`
* `[cut-x] L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.Mid: x <= 20.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.Fast: x <= 12.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.Slow: x <= 12.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen`
* `[admissible] Low_L: [Fast, Slow, MidEco, MidBoost]`
* `[admissible] Mid_L: [MidEco, MidBoost, High]`
* `[admissible] High_L: [High]`
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (110 ms)
* cover `Low_L`: λ = 2, budget 2, admissible ['Fast', 'Slow', 'MidEco', 'MidBoost'], flags {'Fast': 'j--', 'Slow': 'j--', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'jd-', 'PumpOff': '---'}, kinds ['base', 'joint'], path modes ['Fast', 'High', 'MidBoost', 'MidEco', 'Slow'], branching 3, right-only False
    * from `Fast`: `Fast:joint(B=2)->[Fast@1, Fast@1, Slow@1, MidEco@1, MidBoost@1]; Fast:base(B=1); Slow:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
    * from `Slow`: `Slow:joint(B=2)->[Slow@1, Slow@1, MidEco@1, MidBoost@1]; Slow:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
* cover `Mid_L`: λ = 2, budget 2, admissible ['MidEco', 'MidBoost', 'High'], flags {'Fast': '---', 'Slow': '---', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'j--', 'PumpOff': 'j--'}, kinds ['base', 'joint'], path modes ['High', 'MidBoost', 'MidEco'], branching 2, right-only False
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
    * from `High`: `High:joint(B=2)->[High@1, High@1, MidEco@1, MidBoost@1]; High:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
* cover `High_L`: λ = 1, budget 1, admissible ['High'], flags {'Fast': 'jdd', 'Slow': 'jdd', 'MidEco': 'jdd', 'MidBoost': 'jdd', 'High': 'j--', 'PumpOff': 'j--'}, kinds ['base'], path modes ['High'], branching 0, right-only False
    * from `High`: `High:base(B=1)`
* cells: **M1** yes: Low λ=2 (per pairing: {'Fast': '1', 'MidEco': '3/2', 'MidBoost': '1', 'High': '1'}), Mid λ=2 (affine dynamics); **M2** yes: Low B=2 via Fast/MidBoost/MidEco/Slow, Mid B=2 via High/MidBoost/MidEco; **M3** yes: Low branch=3, Mid branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.High: 1 conjunct(s); R.Fast: 2 conjunct(s); R.Slow: 2 conjunct(s); R.MidEco: 2 conjunct(s); R.MidBoost: 2 conjunct(s); R.High: 1 conjunct(s); R.PumpOff: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape; L.Mid: x <= 20.0 kind=closure entry=weakening route=shape; R.Fast: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.Slow: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape; R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape; R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

