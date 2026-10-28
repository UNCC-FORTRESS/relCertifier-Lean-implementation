## Matrix

| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ widened cut | M6L linear-form chain | M7 scenario; dim; invariant; domains |
|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | CERTIFIED (160) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=2 via CRUISE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 2; conjunctive |
| `acc_spoof_limp` | CERTIFIED (249) | no (λ=1 everywhere) | yes: CRUISE B=2 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT | yes: CRUISE branch=2, LIMP branch=2 | vacuous: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE... | no (rows identical; handoff vacuous) | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `acc_tune_lag` | CERTIFIED (180) | yes: CRUISE λ=2 (affine dynamics) | yes: CRUISE B=2 via CRUISE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-controller; dim 2; conjunctive |
| `acc_tune_limp` | CERTIFIED (1035) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=2 via NORMAL +choice COMFORT:hop/SPORT:hop | yes: CRUISE branch=2 | vacuous: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISEN... | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | no (no linear-form atom kept) | degraded-controller; dim 1; conjunctive+linear |
| `bottling_fill_strainer` | CERTIFIED (648) | yes: FILL λ=17/20 (affine dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.FILL: 4 conjunct(s); L.CLOSE: 4 conjunct(s); R.FILL: 4 conju... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `charger_fast_tapers` | CERTIFIED (634) | no (λ=1 everywhere) | yes: PRECHARGE B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FULL +RO, BULK ... | yes: PRECHARGE branch=2, ABSORB branch=2, FAULT branch=2 | yes: pruned PRECHARGE->FAULT, BULK->FAULT; NO_PRUNE=DECLINED | yes: 10/10 handoffs unsat, rows differ | yes: L.PRECHARGE: 2 conjunct(s); L.BULK: 2 conjunct(s); L.ABSORB: 2... | yes: L.PRECHARGE: x <= 20.0 kind=implied-contraction entry=rational... | no (no linear-form atom kept) | degraded-controller; dim 1; linear |
| `elevator_start_discbrake` | CERTIFIED (958) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 7/7 handoffs unsat, rows differ | vacuous: cuts kept (L.LIFT: 8 conjunct(s); L.UP: 6 conjunct(s); L.A... | no (no widened atom kept) | no (no linear-form atom kept) | actuator-change; dim 3; conjunctive |
| `engine_start_highidle` | CERTIFIED (428) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | vacuous: pruned STARTER->ABORT, LIGHTOFF->ABORT but NO_PRUNE=CERTIF... | yes: 10/10 handoffs unsat, rows differ | yes: L.STARTER: 2 conjunct(s); L.LIGHTOFF: 2 conjunct(s); L.SELF: 2... | yes: L.STARTER: n <= 30 kind=implied-contraction entry=rational rou... | no (no linear-form atom kept) | controller-change; dim 1; linear |
| `flaps_slow_approach` | CERTIFIED (322) | yes: EXT λ=1/2 (polynomial dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.EXT: 2 conjunct(s); L.CONF2: 4 conjunct(s); R... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `fuelcell_chp_dos` | CERTIFIED (520) | no (λ=1 everywhere) | yes: LOW B=2 via LOW +choice MED:hop, MED B=2 via HIGH/LOW/MED, HIG... | yes: MED branch=2 | yes: pruned LOW->HIGH, HIGH->LOW; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.LOW: 4 conjunct(s); L.MED: 6 conjunct(s); L.H... | vacuous: widened atoms kept (R.MED: T >= 50.0 kind=closure entry=we... | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `furnace_program_timebase` | CERTIFIED (1130) | yes: PREHEAT λ=4/5, HEAT λ=4/5, SOAK λ=4/5 (affine dynamics) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.PREHEAT: 3 conjunct(s); L.HEAT: 4 conjunct(s); L.SOAK: 4 con... | yes: L.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational ... | no (no linear-form atom kept) | controller-change; dim 2; conjunctive |
| `gantry_speed_zones` | CERTIFIED (1254) | yes: FREE λ=3, APPROACH λ=2 (affine dynamics) | yes: FREE B=3 via MOVE, APPROACH B=2 via MOVE | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.FREE: 4 conjunct(s); L.APPROACH: 4 conjunct(s... | vacuous: widened atoms kept (L.FREE: x <= 0.5 kind=implied-contract... | no (no linear-form atom kept) | controller-refinement; dim 2; conjunctive |
| `grid_ffr_dos` | CERTIFIED (441) | no (λ=1 everywhere) | yes: NORMAL B=3 via FFR/NORMAL, FFR B=3 via FFR | no (max non-self successors at a joint step = 1) | yes: pruned NORMAL->TRIP, FFR->TRIP; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.NORMAL: 7 conjunct(s); L.FFR: 8 conjunct(s); ... | vacuous: widened atoms kept (R.TRIP: x <= -1.5 kind=closure entry=w... | no (no linear-form atom kept) | dos-attack; dim 3; conjunctive |
| `h2_refuel_ambientbias` | CERTIFIED (793) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | vacuous: pruned STAGE1->ABORT, STAGE2->ABORT but NO_PRUNE=CERTIFIED | yes: 12/12 handoffs unsat, rows differ | yes: L.STAGE1: 2 conjunct(s); L.STAGE2: 2 conjunct(s); L.STAGE3: 2 ... | yes: L.STAGE1: p <= 20 kind=implied-contraction entry=rational rout... | no (no linear-form atom kept) | sensor-fault (degraded sensor feeding the end-pressure table); dim 1; linear |
| `hydro_rejection_gatecal` | CERTIFIED (388) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | vacuous: cuts kept (L.ONGRID: 5 conjunct(s); L.REJECT: 6 conjunct(s... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 3; conjunctive |
| `lit_csf21_vehicle_bus` | CERTIFIED (3282) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 3; conjunctive |
| `lit_csf21_vehicle_thermo` | CERTIFIED (1755) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | sensor-attack; dim 3; conjunctive |
| `lit_drl_car_stop` | CERTIFIED (529) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Accel: 1 conjunct(s); L.Coast: 2 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | controller-refinement; dim 2; conjunctive |
| `lit_drl_lane_control` | CERTIFIED (2720) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.AccelLAccel: 2 conjunct(s); L.AccelLBrake: 2 ... | no (no widened atom kept) | no (no linear-form atom kept) | controller-refinement; dim 3; conjunctive |
| `lit_freedm_meter` | CERTIFIED (2338) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.BatD0R0: 2 conjunct(s); L.BatD0R1: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | information-flow; dim 2; conjunctive |
| `lit_girard08_robot` | CERTIFIED (3579) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (R.M1: 2 conjunct(s); R.M2: 1 conjunct(s); R.M3:... | no (no widened atom kept) | no (no linear-form atom kept) | abstraction; dim 6+-4; quadratic+conj |
| `lit_hypercert_vehicle` | CERTIFIED (1021) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Am4: 1 conjunct(s); L.Am2: 1 conjunct(s); L.A... | no (no widened atom kept) | no (no linear-form atom kept) | opacity; dim 2; conjunctive |
| `lit_lz21_vehicle_position` | CERTIFIED (410) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Um: 1 conjunct(s); L.U0: 2 conjunct(s); L.Up:... | no (no widened atom kept) | no (no linear-form atom kept) | opacity; dim 2; conjunctive |
| `lit_nahs25_salt_tank` | CERTIFIED (207) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.On: 1 conjunct(s); L.Off: 1 conjunct(s); R.On: 1 conjunct(s)... | yes: L.Off: xp <= 28.0 kind=closure entry=weakening route=frozen; R... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `platoon_latency` | CERTIFIED (694) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED | yes: 7/7 handoffs unsat, rows differ | vacuous: cuts kept (L.CACC_UP: 4 conjunct(s); L.CACC_DN: 4 conjunct... | vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=clo... | no (no linear-form atom kept) | degraded-network; dim 3+-1; conjunctive |
| `platoon_linkloss` | CERTIFIED (604) | no (λ=1 everywhere) | yes: CACC B=2 via CACC, ACC B=2 via CACC, AEB B=2 via AEB | no (max non-self successors at a joint step = 0) | vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED | yes: 7/7 handoffs unsat, rows differ | vacuous: cuts kept (L.CACC: 4 conjunct(s); L.ACC: 4 conjunct(s); L.... | vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=clo... | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `platoon_profiles` | CERTIFIED (2270) | yes: SPORT λ=6/5 (affine dynamics) | yes: SPORT B=2 via CACC | no (max non-self successors at a joint step = 0) | vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED | yes: 3/3 handoffs unsat, rows differ | vacuous: cuts kept (L.SPORT: 4 conjunct(s); L.AEB: 2 conjunct(s); R... | vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=clo... | no (no linear-form atom kept) | controller-refinement; dim 2; conjunctive |
| `quad_light_lag` | CERTIFIED (187) | yes: CLIMB λ=6/5 (affine dynamics) | yes: CLIMB B=2 via CLIMB | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 3 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `quad_light_profiles` | CERTIFIED (282) | yes: CLIMB λ=6/5 (affine dynamics) | yes: CLIMB B=2 via NORMAL +choice ECO:hop/SPORT:hop | yes: CLIMB branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.NORMAL: 3 conjunct(s)... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 2; conjunctive |
| `reactor_feed_wireless` | CERTIFIED (757) | no (λ=1 everywhere) | yes: F1 B=2 via F1/F2, F2 B=2 via F1/F2/F3, F3 B=2 via F2/F3/F4, F4... | yes: F1 branch=2, F2 branch=2, F3 branch=2, F4 branch=2 | yes: pruned F1->F4, F2->F4, F3->F1, F4->F1; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.F1: 4 conjunct(s); L.F2: 4 conjunct(s); L.F3:... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 2; conjunctive |
| `rover_ladder_2to3` | CERTIFIED (408) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `rover_ladder_3to6` | CERTIFIED (727) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_ladder_6to8` | CERTIFIED (17191) | yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; quadratic+conj |
| `rover_ladder_8to12` | CERTIFIED (31277) | yes: STEEP λ=11/10, MODER λ=11/10, FLAT λ=11/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER, FLAT... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic+conj |
| `rover_patrol_lag` | CERTIFIED (1254) | yes: FAST λ=11/8 (affine dynamics) | yes: FAST B=2 via FAST/MEDIUM_BRISK +RO | yes: FAST branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.SLOW: 1 conjunct(s); L.MEDIUM_ECO: 1 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3+-1; conjunctive |
| `rover_terrain_2to4` | CERTIFIED (2215) | yes: GRAVEL λ=13/10, PAVED λ=27/10 (affine dynamics) | yes: GRAVEL B=2 via GRAVEL/PAVED, PAVED B=3 via PAVED | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 4; conjunctive |
| `rover_terrain_4to6` | CERTIFIED (1117) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_terrain_6to12` | CERTIFIED (2099) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.MUD: 3 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `sat3w_detumble_phases` | CERTIFIED (2790) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE ... | no (max non-self successors at a joint step = 1) | vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 6; quadratic |
| `sat_detumble_phases` | CERTIFIED (4603) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE ... | no (max non-self successors at a joint step = 1) | vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 4; quadratic |
| `sat_detumble_weak` | CERTIFIED (2011) | yes: DETUMBLE λ=4/5 (affine dynamics) | yes: DETUMBLE B=2 via NOMINAL +choice ECONOMY:hop/SURVIVAL:hop | yes: DETUMBLE branch=2 | vacuous: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE but NO... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunc... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | degraded-actuator; dim 4; quadratic |
| `syringe_relay_prearm` | CERTIFIED (1208) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 13/13 handoffs unsat, rows differ | vacuous: cuts kept (L.RUN1: 8 conjunct(s); L.PREARM: 8 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | controller-change; dim 4; conjunctive |
| `tank_dos_3to1` | CERTIFIED (972) | no (λ=1 everywhere) | yes: P2 B=3 via P2/P3, P3 B=3 via P3/P4, P4 B=3 via P4/P5, P5 B=3 v... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.P2: 4 conjunct(s); L.P3: 3 conjunct(s); L.P4: 3 conjunct(s);... | vacuous: widened atoms kept (L.P2: w <= 22.0 kind=implied-contracti... | no (no linear-form atom kept) | dos-attack; dim 2; conjunctive |
| `train_ato_odometry` | CERTIFIED (2287) | yes: PL1 λ=6/5 (per pairing: {'PL1': '39/40', 'PL2': '43/40'}), PL2... | yes: PL1 B=2 via PL1/PL2/PL3, PL2 B=2 via PL1/PL2/PL3 | yes: PL1 branch=2, PL2 branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.PL1: 2 conjunct(s); L.PL2: 2 conjunct(s); L.P... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-sensor; dim 1; conjunctive |
| `tunnel_jetfan_pairout` | CERTIFIED (330) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | yes: L.NORMAL: 6 conjunct(s); L.FIRE: 6 conjunct(s); R.NORMAL: 6 co... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 3; conjunctive |
| `turbine_startup_gearratio` | CERTIFIED (322) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | yes: pruned SPINUP->STOP, RAMP->STOP; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.SPINUP: 2 conjunct(s); L.RAMP: 2 conjunct(s); L.GEN: 1 conju... | yes: L.SPINUP: w <= 9 kind=implied-contraction entry=rational route... | no (no linear-form atom kept) | degraded-controller (configuration error after a gearbox exchange); dim 1; linear |
| `ventilator_vc_cuffleak` | CERTIFIED (274) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 3/3 handoffs unsat, rows differ | vacuous: cuts kept (L.INSP: 3 conjunct(s); L.EXP: 5 conjunct(s); R.... | no (no widened atom kept) | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `watertank` | CERTIFIED (687) | yes: Low λ=2, Mid λ=2 (affine dynamics) | yes: Low B=2 via Low/MidBoost/MidEco, Mid B=2 via High/MidBoost/Mid... | yes: Low branch=2, Mid branch=2 | vacuous: pruned Low->PumpOff but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.H... | vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contract... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `watertank_twospeed` | CERTIFIED (1865) | yes: Low λ=2 (per pairing: {'Fast': '1', 'MidEco': '3/2', 'MidBoost... | yes: Low B=2 via Fast/MidBoost/MidEco/Slow, Mid B=2 via High/MidBoo... | yes: Low branch=3, Mid branch=2 | yes: pruned Fast->PumpOff; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.H... | vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contract... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `zone_lightmass_schedule` | CERTIFIED (253) | yes: COMFORT λ=2, ECONOMY λ=2 (affine dynamics) | yes: COMFORT B=2 via COMFORT +choice ECONOMY:hop/STANDBY:hop, ECONO... | yes: COMFORT branch=2, ECONOMY branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.COMFORT: 2 conjunct(s); L.ECONOMY: 2 conjunct... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 1; conjunctive |

## Totals

| mechanism | benchmarks (non-vacuous) | count |
|---|---|---|
| M1 | `acc_spoof_lag`, `acc_tune_lag`, `acc_tune_limp`, `bottling_fill_strainer`, `flaps_slow_approach`, `furnace_program_timebase`, `gantry_speed_zones`, `platoon_profiles`, `quad_light_lag`, `quad_light_profiles`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_patrol_lag`, `rover_terrain_2to4`, `sat_detumble_weak`, `train_ato_odometry`, `watertank`, `watertank_twospeed`, `zone_lightmass_schedule` | 19 |
| M2 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `charger_fast_tapers`, `fuelcell_chp_dos`, `gantry_speed_zones`, `grid_ffr_dos`, `platoon_linkloss`, `platoon_profiles`, `quad_light_lag`, `quad_light_profiles`, `reactor_feed_wireless`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_patrol_lag`, `rover_terrain_2to4`, `sat3w_detumble_phases`, `sat_detumble_phases`, `sat_detumble_weak`, `tank_dos_3to1`, `train_ato_odometry`, `watertank`, `watertank_twospeed`, `zone_lightmass_schedule` | 25 |
| M3 | `acc_spoof_limp`, `acc_tune_limp`, `charger_fast_tapers`, `fuelcell_chp_dos`, `quad_light_profiles`, `reactor_feed_wireless`, `rover_patrol_lag`, `sat_detumble_weak`, `train_ato_odometry`, `watertank`, `watertank_twospeed`, `zone_lightmass_schedule` | 12 |
| M4 | `charger_fast_tapers`, `fuelcell_chp_dos`, `grid_ffr_dos`, `reactor_feed_wireless`, `turbine_startup_gearratio`, `watertank_twospeed` | 6 |
| M5 | `acc_tune_limp`, `charger_fast_tapers`, `elevator_start_discbrake`, `engine_start_highidle`, `h2_refuel_ambientbias`, `hydro_rejection_gatecal`, `platoon_latency`, `platoon_linkloss`, `platoon_profiles`, `syringe_relay_prearm`, `tunnel_jetfan_pairout`, `ventilator_vc_cuffleak` | 12 |
| M6 | `acc_spoof_limp`, `acc_tune_limp`, `bottling_fill_strainer`, `charger_fast_tapers`, `engine_start_highidle`, `furnace_program_timebase`, `h2_refuel_ambientbias`, `lit_nahs25_salt_tank`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_terrain_2to4`, `rover_terrain_4to6`, `rover_terrain_6to12`, `sat3w_detumble_phases`, `sat_detumble_phases`, `tank_dos_3to1`, `tunnel_jetfan_pairout`, `turbine_startup_gearratio` | 18 |
| M6+ | `charger_fast_tapers`, `engine_start_highidle`, `furnace_program_timebase`, `h2_refuel_ambientbias`, `lit_nahs25_salt_tank`, `turbine_startup_gearratio` | 6 |
| M6L |  | 0 |
| per-mode domains |  | 0 |

## Proposed Table-1 grouping

| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; widened cuts; linear-form chains; per-mode domains) |
|---|---|---|---|---|---|
| ACC under sensor spoofing / retune | 4 | 1, 2 | conjunctive, conjunctive+linear | affine | modes 1-2 / 1-4; 0 with a pruned fallback; 1 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Quadrotor climb, lighter airframe | 2 | 2, 3 | conjunctive | affine | modes 1-1 / 1-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Platoon follower (CACC: link loss, latency, profiles) | 3 | 2, 3/2 | conjunctive | affine | modes 2-3 / 2-2; 0 with a pruned fallback; 3 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rover patrol (zones) | 1 | 3/2 | conjunctive | affine | modes 4-4 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Gantry speed zones (multi-cycle matching) | 1 | 2 | conjunctive | affine | modes 3-3 / 1-1; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rover ladder | 4 | 3, 6, 8, 12 | conjunctive, quadratic+conj | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Terrain chain | 3 | 4, 6, 12 | conjunctive | affine + polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 3 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Watertank | 2 | 1 | conjunctive | affine | modes 3-3 / 5-6; 1 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Tank under sampling DoS | 1 | 2 | conjunctive | polynomial | modes 4-4 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Turbofan ground start | 1 | 1 | linear | affine | modes 5-5 / 5-5; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Train speed control (ATO) | 1 | 1 | conjunctive | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Wind turbine start-up | 1 | 1 | linear | affine | modes 4-4 / 4-4; 1 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Fuel-cell CHP current levels | 1 | 2 | conjunctive | affine | modes 3-3 / 3-3; 1 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Elevator trip | 1 | 3 | conjunctive | affine | modes 4-4 / 4-4; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Heat-treatment furnace program | 1 | 2 | conjunctive | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Syringe-pump relay | 1 | 4 | conjunctive | affine | modes 6-6 / 4-4; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Hydro unit load rejection | 1 | 3 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Volume-controlled ventilation | 1 | 2 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Road-tunnel ventilation through a fire alarm | 1 | 3 | conjunctive | polynomial | modes 2-2 / 2-2; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Island grid fast frequency response (DoS on the FFR link) | 1 | 3 | conjunctive | affine | modes 2-2 / 3-3; 1 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Bottle filler (clogged product strainer) | 1 | 2 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Airliner flap extension (one hydraulic system lost) | 1 | 2 | conjunctive | polynomial | modes 2-2 / 2-2; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| DC fast charger (raised current limit) | 1 | 1 | linear | affine | modes 5-5 / 6-6; 1 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rigid-body detumbling (polynomial) | 3 | 4, 6 | quadratic | affine + polynomial | modes 1-2 / 3-4; 0 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Building zone heating (lightweight construction) | 1 | 1 | conjunctive | affine | modes 2-2 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Hydrogen refuelling (sensor bias) | 1 | 1 | linear | affine | modes 6-6 / 6-6; 0 with a pruned fallback; 1 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Exothermic reactor feed interlock | 1 | 2 | conjunctive | affine | modes 4-4 / 4-4; 1 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Literature | 9 | 1, 2, 3, 6/2 | conjunctive, quadratic+conj | affine | modes 2-12 / 2-12; 0 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| **total** | **50** | | | | |

## Duplicate check

no two benchmarks normalize to the same model; no two benchmarks differ only in tolerance constants (rows' numerals masked)

## Timing

| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 2/2 | CERTIFIED | 160 | 0.43 | - | - | - | - |
| `acc_spoof_limp` | 1/1 | CERTIFIED | 249 | 0.51 | - | - | - | - |
| `acc_tune_lag` | 2/2 | CERTIFIED | 180 | 0.45 | - | - | - | - |
| `acc_tune_limp` | 1/1 | CERTIFIED | 1035 | 1.24 | - | - | - | - |
| `bottling_fill_strainer` | 2/2 | CERTIFIED | 648 | 0.88 | - | - | - | - |
| `charger_fast_tapers` | 1/1 | CERTIFIED | 634 | 0.89 | - | - | - | - |
| `elevator_start_discbrake` | 3/3 | CERTIFIED | 958 | 1.22 | - | - | - | - |
| `engine_start_highidle` | 1/1 | CERTIFIED | 428 | 0.68 | - | - | - | - |
| `flaps_slow_approach` | 2/2 | CERTIFIED | 322 | 0.57 | - | - | - | - |
| `fuelcell_chp_dos` | 2/2 | CERTIFIED | 520 | 0.8 | - | - | - | - |
| `furnace_program_timebase` | 2/2 | CERTIFIED | 1130 | 1.31 | - | - | - | - |
| `gantry_speed_zones` | 2/2 | CERTIFIED | 1254 | 1.52 | - | - | - | - |
| `grid_ffr_dos` | 3/3 | CERTIFIED | 441 | 0.7 | - | - | - | - |
| `h2_refuel_ambientbias` | 1/1 | CERTIFIED | 793 | 1.05 | - | - | - | - |
| `hydro_rejection_gatecal` | 3/3 | CERTIFIED | 388 | 0.6 | - | - | - | - |
| `lit_csf21_vehicle_bus` | 3/3 | CERTIFIED | 3282 | 3.56 | - | - | - | - |
| `lit_csf21_vehicle_thermo` | 3/3 | CERTIFIED | 1755 | 2.02 | - | - | - | - |
| `lit_drl_car_stop` | 2/2 | CERTIFIED | 529 | 0.79 | - | - | - | - |
| `lit_drl_lane_control` | 3/3 | CERTIFIED | 2720 | 2.98 | - | - | - | - |
| `lit_freedm_meter` | 2/2 | CERTIFIED | 2338 | 2.6 | - | - | - | - |
| `lit_girard08_robot` | 6/2 | CERTIFIED | 3579 | 3.76 | - | - | - | - |
| `lit_hypercert_vehicle` | 2/2 | CERTIFIED | 1021 | 1.27 | - | - | - | - |
| `lit_lz21_vehicle_position` | 2/2 | CERTIFIED | 410 | 0.64 | - | - | - | - |
| `lit_nahs25_salt_tank` | 1/1 | CERTIFIED | 207 | 0.44 | - | - | - | - |
| `platoon_latency` | 3/2 | CERTIFIED | 694 | 0.96 | - | - | - | - |
| `platoon_linkloss` | 2/2 | CERTIFIED | 604 | 0.78 | - | - | - | - |
| `platoon_profiles` | 2/2 | CERTIFIED | 2270 | 2.53 | - | - | - | - |
| `quad_light_lag` | 3/3 | CERTIFIED | 187 | 0.4 | - | - | - | - |
| `quad_light_profiles` | 2/2 | CERTIFIED | 282 | 0.53 | - | - | - | - |
| `reactor_feed_wireless` | 2/2 | CERTIFIED | 757 | 1.02 | - | - | - | - |
| `rover_ladder_2to3` | 3/3 | CERTIFIED | 408 | 0.67 | - | - | - | - |
| `rover_ladder_3to6` | 6/6 | CERTIFIED | 727 | 0.98 | - | - | - | - |
| `rover_ladder_6to8` | 8/8 | CERTIFIED | 17191 | 17.46 | - | - | - | - |
| `rover_ladder_8to12` | 12/12 | CERTIFIED | 31277 | 31.55 | - | - | - | - |
| `rover_patrol_lag` | 3/2 | CERTIFIED | 1254 | 1.49 | - | - | - | - |
| `rover_terrain_2to4` | 4/4 | CERTIFIED | 2215 | 2.47 | - | - | - | - |
| `rover_terrain_4to6` | 6/6 | CERTIFIED | 1117 | 1.38 | - | - | - | - |
| `rover_terrain_6to12` | 12/12 | CERTIFIED | 2099 | 2.29 | - | - | - | - |
| `sat3w_detumble_phases` | 6/6 | CERTIFIED | 2790 | 3.02 | - | - | - | - |
| `sat_detumble_phases` | 4/4 | CERTIFIED | 4603 | 4.86 | - | - | - | - |
| `sat_detumble_weak` | 4/4 | CERTIFIED | 2011 | 2.23 | - | - | - | - |
| `syringe_relay_prearm` | 4/4 | CERTIFIED | 1208 | 1.48 | - | - | - | - |
| `tank_dos_3to1` | 2/2 | CERTIFIED | 972 | 1.23 | - | - | - | - |
| `train_ato_odometry` | 1/1 | CERTIFIED | 2287 | 2.51 | - | - | - | - |
| `tunnel_jetfan_pairout` | 3/3 | CERTIFIED | 330 | 0.6 | - | - | - | - |
| `turbine_startup_gearratio` | 1/1 | CERTIFIED | 322 | 0.57 | - | - | - | - |
| `ventilator_vc_cuffleak` | 2/2 | CERTIFIED | 274 | 0.53 | - | - | - | - |
| `watertank` | 1/1 | CERTIFIED | 687 | 0.95 | - | - | - | - |
| `watertank_twospeed` | 1/1 | CERTIFIED | 1865 | 2.1 | - | - | - | - |
| `zone_lightmass_schedule` | 1/1 | CERTIFIED | 253 | 0.48 | - | - | - | - |
| **total** | | | **103665** | | | **0** | | |

## Per-benchmark run records

### `acc_spoof_lag`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 2/2; modes L/R 1/1; εL/εR 0.1/0.1; λ ∈ [1.5, 1.5]; invariant shape conjunctive; rows identical: True; normalized md5 `e49a92cb5bb5`
* `relcert`: **CERTIFIED** (160 ms); `[prune] acc_spoof_lag: []`; NO_PRUNE: **CERTIFIED** (126 ms); NO_CUT: **CERTIFIED** (124 ms); NO_IMPLIED_CUT: **CERTIFIED** (157 ms); NO_LINEAR_CUT: **CERTIFIED** (159 ms); domains: uniform
* `[cut] L.CRUISE: 4 conjunct(s)`
* `[cut] R.CRUISE: 4 conjunct(s)`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (99 ms)
* cover `CRUISE_L`: λ = 3/2, budget 2, admissible ['CRUISE'], flags {'CRUISE': 'j--'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=2 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `acc_spoof_limp`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `d99d0500d684`
* `relcert`: **CERTIFIED** (249 ms); `[prune] acc_spoof_limp: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (202 ms); NO_CUT: **DECLINED** (232 ms); NO_IMPLIED_CUT: **CERTIFIED** (242 ms); NO_LINEAR_CUT: **CERTIFIED** (264 ms); domains: uniform
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
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (101 ms)
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

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 2/2; modes L/R 1/1; εL/εR 0.1/0.1; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8679340248f0`
* `relcert`: **CERTIFIED** (180 ms); `[prune] acc_tune_lag: []`; NO_PRUNE: **CERTIFIED** (195 ms); NO_CUT: **CERTIFIED** (85 ms); NO_IMPLIED_CUT: **CERTIFIED** (125 ms); NO_LINEAR_CUT: **CERTIFIED** (139 ms); domains: uniform
* `[cut] L.CRUISE: 4 conjunct(s)`
* `[cut] R.CRUISE: 4 conjunct(s)`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (95 ms)
* cover `CRUISE_L`: λ = 2, budget 2, admissible ['CRUISE'], flags {'CRUISE': 'j--'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=2 (affine dynamics); **M2** yes: CRUISE B=2 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 4 conjunct(s); R.CRUISE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `acc_tune_limp`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 2/4; εL/εR 0.1/0.1; λ ∈ [1.0, 6.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `0cd6c908b86f`
* `relcert`: **CERTIFIED** (1035 ms); `[prune] acc_tune_limp: [NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (1063 ms); NO_CUT: **DECLINED** (1385 ms); NO_IMPLIED_CUT: **CERTIFIED** (1043 ms); NO_LINEAR_CUT: **CERTIFIED** (1049 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.COMFORT: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, COMFORT, SPORT]`
* `[admissible] LIMP_L: [NORMAL, COMFORT, SPORT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (80 ms)
* cover `CRUISE_L`: λ = 3/2, budget 2, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j--', 'COMFORT': '---', 'SPORT': '---', 'DISENGAGE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `COMFORT`: `COMFORT:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `SPORT`: `SPORT:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
* cover `LIMP_L`: λ = 1, budget 1, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j--', 'COMFORT': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 0, right-only False
    * from `NORMAL`: `NORMAL:base(B=1)`
    * from `COMFORT`: `COMFORT:base(B=1)`
    * from `SPORT`: `SPORT:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=2 via NORMAL +choice COMFORT:hop/SPORT:hop; **M3** yes: CRUISE branch=2; **M4** vacuous: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `bottling_fill_strainer`

* family: Bottle filler (clogged product strainer); scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.005/0.005; λ ∈ [0.8, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `7eda705fff55`
* `relcert`: **CERTIFIED** (648 ms); `[prune] bottling_fill_strainer: []`; NO_PRUNE: **CERTIFIED** (656 ms); NO_CUT: **DECLINED** (1648 ms); NO_IMPLIED_CUT: **CERTIFIED** (663 ms); NO_LINEAR_CUT: **CERTIFIED** (645 ms); domains: uniform
* `[cut] L.FILL: 4 conjunct(s)`
* `[cut] L.CLOSE: 4 conjunct(s)`
* `[cut] R.FILL: 4 conjunct(s)`
* `[cut] R.CLOSE: 4 conjunct(s)`
* `[admissible] FILL_L: [FILL]`
* `[admissible] CLOSE_L: [CLOSE]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (82 ms)
* cover `FILL_L`: λ = 17/20, budget 1, admissible ['FILL'], flags {'FILL': 'j--', 'CLOSE': '---'}, kinds ['base'], path modes ['FILL'], branching 0, right-only False
    * from `FILL`: `FILL:base(B=1)`
* cover `CLOSE_L`: λ = 1, budget 1, admissible ['CLOSE'], flags {'FILL': '---', 'CLOSE': 'j--'}, kinds ['base'], path modes ['CLOSE'], branching 0, right-only False
    * from `CLOSE`: `CLOSE:base(B=1)`
* cells: **M1** yes: FILL λ=17/20 (affine dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.FILL: 4 conjunct(s); L.CLOSE: 4 conjunct(s); R.FILL: 4 conjunct(s); R.CLOSE: 4 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `charger_fast_tapers`

* family: DC fast charger (raised current limit); scenario: degraded-controller; dims L/R 1/1; modes L/R 5/6; εL/εR 0.012/0.006; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: False; normalized md5 `7407d2c54b28`
* `relcert`: **CERTIFIED** (634 ms); `[prune] charger_fast_tapers: [PRECHARGE->FAULT, BULK->FAULT]`; NO_PRUNE: **DECLINED** (1761 ms); NO_CUT: **DECLINED** (752 ms); NO_IMPLIED_CUT: **DECLINED** (806 ms); NO_LINEAR_CUT: **CERTIFIED** (551 ms); domains: uniform
* `[cut] L.PRECHARGE: 2 conjunct(s)`
* `[cut] L.BULK: 2 conjunct(s)`
* `[cut] L.ABSORB: 2 conjunct(s)`
* `[cut] L.FULL: 1 conjunct(s)`
* `[cut] L.FAULT: 1 conjunct(s)`
* `[cut] R.PRECHARGE: 2 conjunct(s)`
* `[cut] R.BULK: 2 conjunct(s)`
* `[cut] R.ABSORB_SLOW: 2 conjunct(s)`
* `[cut] R.ABSORB_FAST: 2 conjunct(s)`
* `[cut] R.FULL: 1 conjunct(s)`
* `[cut] R.FAULT: 1 conjunct(s)`
* `[cut-x] L.PRECHARGE: x <= 20.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.PRECHARGE: x <= 20.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[admissible] PRECHARGE_L: [PRECHARGE, BULK, ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] BULK_L: [PRECHARGE, BULK, ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] ABSORB_L: [BULK, ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] FULL_L: [ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] FAULT_L: [PRECHARGE, BULK, ABSORB_SLOW, ABSORB_FAST, FULL, FAULT]`
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (112 ms)
* cover `PRECHARGE_L`: λ = 1, budget 2, admissible ['PRECHARGE', 'BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'PRECHARGE': '-dd', 'BULK': 'jdd', 'ABSORB_SLOW': 'jdd', 'ABSORB_FAST': 'jdd', 'FULL': 'j--', 'FAULT': '---'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL', 'PRECHARGE'], branching 2, right-only True
    * from `PRECHARGE`: `PRECHARGE:repoDyn(B=2,preJ)->[BULK@2]; BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:base(B=1); ABSORB_FAST:base(B=1)`
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:base(B=1); ABSORB_FAST:base(B=1)`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `BULK_L`: λ = 1, budget 2, admissible ['PRECHARGE', 'BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'PRECHARGE': '-dd', 'BULK': '-dd', 'ABSORB_SLOW': '-dd', 'ABSORB_FAST': '-dd', 'FULL': 'j--', 'FAULT': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL', 'PRECHARGE'], branching 0, right-only True
    * from `PRECHARGE`: `PRECHARGE:repoDyn(B=2,preJ)->[BULK@2]; BULK:repoDyn(B=2,preJ)->[ABSORB_SLOW@2, ABSORB_FAST@2]; ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1); ABSORB_FAST:repoDyn(B=2,preJ)->[FULL@2]`
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB_SLOW@2, ABSORB_FAST@2]; ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1); ABSORB_FAST:repoDyn(B=2,preJ)->[FULL@2]`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'PRECHARGE': 'jdd', 'BULK': 'jdd', 'ABSORB_SLOW': '-dd', 'ABSORB_FAST': 'jdd', 'FULL': 'j--', 'FAULT': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL'], branching 2, right-only True
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:repoDyn(B=1,postJ)->[FULL@1]; FULL:base(B=1); ABSORB_FAST:base(B=1)`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'PRECHARGE': 'jdd', 'BULK': 'jdd', 'ABSORB_SLOW': 'jdd', 'ABSORB_FAST': 'jdd', 'FULL': 'j--', 'FAULT': 'j--'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'FULL'], branching 1, right-only False
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FAULT_L`: λ = 1, budget 2, admissible ['PRECHARGE', 'BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL', 'FAULT'], flags {'PRECHARGE': 'jdd', 'BULK': 'jdd', 'ABSORB_SLOW': 'jdd', 'ABSORB_FAST': 'jdd', 'FULL': 'j--', 'FAULT': 'j--'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FAULT', 'FULL', 'PRECHARGE'], branching 2, right-only False
    * from `PRECHARGE`: `PRECHARGE:joint(B=2)->[PRECHARGE@1, BULK@1, PRECHARGE@1]; PRECHARGE:base(B=1); BULK:base(B=1)`
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:base(B=1); ABSORB_FAST:base(B=1)`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `FAULT`: `FAULT:joint(B=2)->[FAULT@1, FAULT@1]; FAULT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: PRECHARGE B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FULL +RO, BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/BULK/FULL +RO, FULL B=2 via ABSORB_FAST/ABSORB_SLOW/FULL, FAULT B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FAULT/FULL/PRECHARGE; **M3** yes: PRECHARGE branch=2, ABSORB branch=2, FAULT branch=2; **M4** yes: pruned PRECHARGE->FAULT, BULK->FAULT; NO_PRUNE=DECLINED; **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.PRECHARGE: 2 conjunct(s); L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); L.FAULT: 1 conjunct(s); R.PRECHARGE: 2 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB_SLOW: 2 conjunct(s); R.ABSORB_FAST: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.PRECHARGE: x <= 20.0 kind=implied-contraction entry=rational route=shape; L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.FAULT: x <= 10.0 kind=closure entry=weakening route=shape; R.PRECHARGE: x <= 20.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `elevator_start_discbrake`

* family: Elevator trip; scenario: actuator-change; dims L/R 3/3; modes L/R 4/4; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `18047bc26501`
* `relcert`: **CERTIFIED** (958 ms); `[prune] elevator_start_discbrake: []`; NO_PRUNE: **CERTIFIED** (984 ms); NO_CUT: **CERTIFIED** (984 ms); NO_IMPLIED_CUT: **CERTIFIED** (930 ms); NO_LINEAR_CUT: **CERTIFIED** (987 ms); domains: uniform
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
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (101 ms)
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

* family: Turbofan ground start; scenario: controller-change; dims L/R 1/1; modes L/R 5/5; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape linear; rows identical: False; normalized md5 `c6f397fa50cc`
* `relcert`: **CERTIFIED** (428 ms); `[prune] engine_start_highidle: [STARTER->ABORT, LIGHTOFF->ABORT]`; NO_PRUNE: **CERTIFIED** (444 ms); NO_CUT: **DECLINED** (162 ms); NO_IMPLIED_CUT: **DECLINED** (145 ms); NO_LINEAR_CUT: **CERTIFIED** (498 ms); domains: uniform
* `[cut] L.STARTER: 2 conjunct(s)`
* `[cut] L.LIGHTOFF: 2 conjunct(s)`
* `[cut] L.SELF: 2 conjunct(s)`
* `[cut] L.IDLE: 1 conjunct(s)`
* `[cut] L.ABORT: 1 conjunct(s)`
* `[cut] R.STARTER: 2 conjunct(s)`
* `[cut] R.LIGHTOFF: 2 conjunct(s)`
* `[cut] R.SELF: 2 conjunct(s)`
* `[cut] R.IDLE: 1 conjunct(s)`
* `[cut] R.ABORT: 1 conjunct(s)`
* `[cut-x] L.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.SELF: n <= 66 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABORT: n <= 5.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.SELF: n <= 62 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABORT: n <= 5.0 kind=closure entry=weakening route=diB`
* `[admissible] STARTER_L: [STARTER, LIGHTOFF, SELF, IDLE]`
* `[admissible] LIGHTOFF_L: [LIGHTOFF, SELF, IDLE]`
* `[admissible] SELF_L: [LIGHTOFF, SELF, IDLE]`
* `[admissible] IDLE_L: [SELF, IDLE]`
* `[admissible] ABORT_L: [STARTER, LIGHTOFF, SELF, IDLE, ABORT]`
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (113 ms)
* cover `STARTER_L`: λ = 1, budget 1, admissible ['STARTER', 'LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': 'jdd', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': '---'}, kinds ['base'], path modes ['IDLE', 'LIGHTOFF', 'SELF', 'STARTER'], branching 0, right-only False
    * from `STARTER`: `STARTER:base(B=1)`
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `LIGHTOFF_L`: λ = 1, budget 1, admissible ['LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': '-dd', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['IDLE', 'LIGHTOFF', 'SELF'], branching 0, right-only False
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `SELF_L`: λ = 1, budget 1, admissible ['LIGHTOFF', 'SELF', 'IDLE'], flags {'STARTER': 'jdd', 'LIGHTOFF': '-dd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base', 'repoDyn'], path modes ['IDLE', 'LIGHTOFF', 'SELF'], branching 0, right-only True
    * from `LIGHTOFF`: `LIGHTOFF:repoDyn(B=1,preJ)->[SELF@1]; SELF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `IDLE_L`: λ = 1, budget 1, admissible ['SELF', 'IDLE'], flags {'STARTER': 'jdd', 'LIGHTOFF': 'jdd', 'SELF': '-dd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base', 'repoDyn'], path modes ['IDLE', 'SELF'], branching 0, right-only True
    * from `SELF`: `SELF:repoDyn(B=1,preJ)->[IDLE@1]; IDLE:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
* cover `ABORT_L`: λ = 1, budget 1, admissible ['STARTER', 'LIGHTOFF', 'SELF', 'IDLE', 'ABORT'], flags {'STARTER': 'jdd', 'LIGHTOFF': 'jdd', 'SELF': 'jdd', 'IDLE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['ABORT', 'IDLE', 'LIGHTOFF', 'SELF', 'STARTER'], branching 0, right-only False
    * from `STARTER`: `STARTER:base(B=1)`
    * from `LIGHTOFF`: `LIGHTOFF:base(B=1)`
    * from `SELF`: `SELF:base(B=1)`
    * from `IDLE`: `IDLE:base(B=1)`
    * from `ABORT`: `ABORT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned STARTER->ABORT, LIGHTOFF->ABORT but NO_PRUNE=CERTIFIED; **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.STARTER: 2 conjunct(s); L.LIGHTOFF: 2 conjunct(s); L.SELF: 2 conjunct(s); L.IDLE: 1 conjunct(s); L.ABORT: 1 conjunct(s); R.STARTER: 2 conjunct(s); R.LIGHTOFF: 2 conjunct(s); R.SELF: 2 conjunct(s); R.IDLE: 1 conjunct(s); R.ABORT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape; L.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape; L.SELF: n <= 66 kind=implied-contraction entry=rational route=shape; L.ABORT: n <= 5.0 kind=closure entry=weakening route=diB; R.STARTER: n <= 30 kind=implied-contraction entry=rational route=shape; R.LIGHTOFF: n <= 55 kind=implied-contraction entry=rational route=shape; R.SELF: n <= 62 kind=implied-contraction entry=rational route=shape; R.ABORT: n <= 5.0 kind=closure entry=weakening route=diB; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `flaps_slow_approach`

* family: Airliner flap extension (one hydraulic system lost); scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [0.5, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a42871de2784`
* `relcert`: **CERTIFIED** (322 ms); `[prune] flaps_slow_approach: []`; NO_PRUNE: **CERTIFIED** (336 ms); NO_CUT: **CERTIFIED** (291 ms); NO_IMPLIED_CUT: **CERTIFIED** (264 ms); NO_LINEAR_CUT: **CERTIFIED** (321 ms); domains: uniform
* `[cut] L.EXT: 2 conjunct(s)`
* `[cut] L.CONF2: 4 conjunct(s)`
* `[cut] R.EXT: 2 conjunct(s)`
* `[cut] R.CONF2: 4 conjunct(s)`
* `[admissible] EXT_L: [EXT]`
* `[admissible] CONF2_L: [CONF2]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (99 ms)
* cover `EXT_L`: λ = 1/2, budget 1, admissible ['EXT'], flags {'EXT': 'j--', 'CONF2': '---'}, kinds ['base'], path modes ['EXT'], branching 0, right-only False
    * from `EXT`: `EXT:base(B=1)`
* cover `CONF2_L`: λ = 1, budget 1, admissible ['CONF2'], flags {'EXT': '---', 'CONF2': 'j--'}, kinds ['base'], path modes ['CONF2'], branching 0, right-only False
    * from `CONF2`: `CONF2:base(B=1)`
* cells: **M1** yes: EXT λ=1/2 (polynomial dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.EXT: 2 conjunct(s); L.CONF2: 4 conjunct(s); R.EXT: 2 conjunct(s); R.CONF2: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `fuelcell_chp_dos`

* family: Fuel-cell CHP current levels; scenario: dos-attack; dims L/R 2/2; modes L/R 3/3; εL/εR 20.0/10.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `f5026c69d3b9`
* `relcert`: **CERTIFIED** (520 ms); `[prune] fuelcell_chp_dos: [LOW->HIGH, HIGH->LOW]`; NO_PRUNE: **DECLINED** (264 ms); NO_CUT: **CERTIFIED** (403 ms); NO_IMPLIED_CUT: **CERTIFIED** (498 ms); NO_LINEAR_CUT: **CERTIFIED** (490 ms); domains: uniform
* `[cut] L.LOW: 4 conjunct(s)`
* `[cut] L.MED: 6 conjunct(s)`
* `[cut] L.HIGH: 4 conjunct(s)`
* `[cut] R.LOW: 4 conjunct(s)`
* `[cut] R.MED: 6 conjunct(s)`
* `[cut] R.HIGH: 4 conjunct(s)`
* `[cut-x] R.MED: T >= 50.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.MED: T <= 80.0 kind=closure entry=weakening route=diB`
* `[admissible] LOW_L: [LOW, MED]`
* `[admissible] MED_L: [LOW, MED, HIGH]`
* `[admissible] HIGH_L: [MED, HIGH]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (91 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** yes: LOW B=2 via LOW +choice MED:hop, MED B=2 via HIGH/LOW/MED, HIGH B=2 via HIGH +choice MED:hop; **M3** yes: MED branch=2; **M4** yes: pruned LOW->HIGH, HIGH->LOW; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.LOW: 4 conjunct(s); L.MED: 6 conjunct(s); L.HIGH: 4 conjunct(s); R.LOW: 4 conjunct(s); R.MED: 6 conjunct(s); R.HIGH: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.MED: T >= 50.0 kind=closure entry=weakening route=diB; R.MED: T <= 80.0 kind=closure entry=weakening route=diB) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `furnace_program_timebase`

* family: Heat-treatment furnace program; scenario: controller-change; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [0.8, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `854fb41fd15a`
* `relcert`: **CERTIFIED** (1130 ms); `[prune] furnace_program_timebase: []`; NO_PRUNE: **CERTIFIED** (1139 ms); NO_CUT: **DECLINED** (3029 ms); NO_IMPLIED_CUT: **DECLINED** (3789 ms); NO_LINEAR_CUT: **CERTIFIED** (1122 ms); domains: uniform
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
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `PREHEAT_L`: λ = 4/5, budget 1, admissible ['PREHEAT'], flags {'PREHEAT': 'j--', 'HEAT': '---', 'SOAK': 'j--'}, kinds ['base'], path modes ['PREHEAT'], branching 0, right-only False
    * from `PREHEAT`: `PREHEAT:base(B=1)`
* cover `HEAT_L`: λ = 4/5, budget 1, admissible ['HEAT'], flags {'PREHEAT': '---', 'HEAT': 'j--', 'SOAK': '---'}, kinds ['base'], path modes ['HEAT'], branching 0, right-only False
    * from `HEAT`: `HEAT:base(B=1)`
* cover `SOAK_L`: λ = 4/5, budget 1, admissible ['SOAK'], flags {'PREHEAT': 'jdd', 'HEAT': '---', 'SOAK': 'j--'}, kinds ['base'], path modes ['SOAK'], branching 0, right-only False
    * from `SOAK`: `SOAK:base(B=1)`
* cells: **M1** yes: PREHEAT λ=4/5, HEAT λ=4/5, SOAK λ=4/5 (affine dynamics); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.PREHEAT: 3 conjunct(s); L.HEAT: 4 conjunct(s); L.SOAK: 4 conjunct(s); R.PREHEAT: 3 conjunct(s); R.HEAT: 4 conjunct(s); R.SOAK: 4 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape; L.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape; R.PREHEAT: s <= 650.0 kind=implied-contraction entry=rational route=shape; R.HEAT: s <= 870.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `gantry_speed_zones`

* family: Gantry speed zones (multi-cycle matching); scenario: controller-refinement; dims L/R 2/2; modes L/R 3/1; εL/εR 0.1/0.1; λ ∈ [1.0, 3.0]; invariant shape conjunctive; rows identical: True; normalized md5 `62c25fa54533`
* `relcert`: **CERTIFIED** (1254 ms); `[prune] gantry_speed_zones: []`; NO_PRUNE: **CERTIFIED** (1257 ms); NO_CUT: **CERTIFIED** (822 ms); NO_IMPLIED_CUT: **CERTIFIED** (827 ms); NO_LINEAR_CUT: **CERTIFIED** (1248 ms); domains: uniform
* `[cut] L.FREE: 4 conjunct(s)`
* `[cut] L.APPROACH: 4 conjunct(s)`
* `[cut] L.PLACE: 4 conjunct(s)`
* `[cut] R.MOVE: 4 conjunct(s)`
* `[cut-x] L.FREE: x <= 0.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.APPROACH: x <= 0.5 kind=implied-contraction entry=rational route=shape`
* `[admissible] FREE_L: [MOVE]`
* `[admissible] APPROACH_L: [MOVE]`
* `[admissible] PLACE_L: [MOVE]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (76 ms)
* cover `FREE_L`: λ = 3, budget 3, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base', 'joint'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:joint(B=3)->[MOVE@2, MOVE@2]; MOVE:joint(B=2)->[MOVE@1, MOVE@1]; MOVE:base(B=1)`
* cover `APPROACH_L`: λ = 2, budget 2, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base', 'joint'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:joint(B=2)->[MOVE@1, MOVE@1]; MOVE:base(B=1)`
* cover `PLACE_L`: λ = 1, budget 1, admissible ['MOVE'], flags {'MOVE': 'j--'}, kinds ['base'], path modes ['MOVE'], branching 0, right-only False
    * from `MOVE`: `MOVE:base(B=1)`
* cells: **M1** yes: FREE λ=3, APPROACH λ=2 (affine dynamics); **M2** yes: FREE B=3 via MOVE, APPROACH B=2 via MOVE; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.FREE: 4 conjunct(s); L.APPROACH: 4 conjunct(s); L.PLACE: 4 conjunct(s); R.MOVE: 4 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.FREE: x <= 0.5 kind=implied-contraction entry=rational route=shape; L.APPROACH: x <= 0.5 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `grid_ffr_dos`

* family: Island grid fast frequency response (DoS on the FFR link); scenario: dos-attack; dims L/R 3/3; modes L/R 2/3; εL/εR 0.3/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `7ff8d420e339`
* `relcert`: **CERTIFIED** (441 ms); `[prune] grid_ffr_dos: [NORMAL->TRIP, FFR->TRIP]`; NO_PRUNE: **DECLINED** (223 ms); NO_CUT: **CERTIFIED** (411 ms); NO_IMPLIED_CUT: **CERTIFIED** (435 ms); NO_LINEAR_CUT: **CERTIFIED** (416 ms); domains: uniform
* `[cut] L.NORMAL: 7 conjunct(s)`
* `[cut] L.FFR: 8 conjunct(s)`
* `[cut] R.NORMAL: 7 conjunct(s)`
* `[cut] R.FFR: 8 conjunct(s)`
* `[cut] R.TRIP: 6 conjunct(s)`
* `[cut-x] R.TRIP: x <= -1.5 kind=closure entry=weakening route=diB`
* `[admissible] NORMAL_L: [NORMAL, FFR]`
* `[admissible] FFR_L: [FFR]`
* `--handoff`: 3/3 checked, 3 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `NORMAL_L`: λ = 1, budget 3, admissible ['NORMAL', 'FFR'], flags {'NORMAL': 'j--', 'FFR': 'j--', 'TRIP': '---'}, kinds ['base', 'joint'], path modes ['FFR', 'NORMAL'], branching 1, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, FFR@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, FFR@1]; NORMAL:base(B=1); FFR:base(B=1); FFR:joint(B=2)->[FFR@1, FFR@1]`
    * from `FFR`: `FFR:joint(B=3)->[FFR@2, FFR@2]; FFR:joint(B=2)->[FFR@1, FFR@1]; FFR:base(B=1)`
* cover `FFR_L`: λ = 1, budget 3, admissible ['FFR'], flags {'NORMAL': '---', 'FFR': 'j--', 'TRIP': '---'}, kinds ['base', 'joint'], path modes ['FFR'], branching 0, right-only False
    * from `FFR`: `FFR:joint(B=3)->[FFR@2, FFR@2]; FFR:joint(B=2)->[FFR@1, FFR@1]; FFR:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: NORMAL B=3 via FFR/NORMAL, FFR B=3 via FFR; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned NORMAL->TRIP, FFR->TRIP; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.NORMAL: 7 conjunct(s); L.FFR: 8 conjunct(s); R.NORMAL: 7 conjunct(s); R.FFR: 8 conjunct(s); R.TRIP: 6 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.TRIP: x <= -1.5 kind=closure entry=weakening route=diB) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `h2_refuel_ambientbias`

* family: Hydrogen refuelling (sensor bias); scenario: sensor-fault (degraded sensor feeding the end-pressure table); dims L/R 1/1; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: False; normalized md5 `c01ac84f2a2b`
* `relcert`: **CERTIFIED** (793 ms); `[prune] h2_refuel_ambientbias: [STAGE1->ABORT, STAGE2->ABORT]`; NO_PRUNE: **CERTIFIED** (755 ms); NO_CUT: **DECLINED** (685 ms); NO_IMPLIED_CUT: **DECLINED** (841 ms); NO_LINEAR_CUT: **CERTIFIED** (719 ms); domains: uniform
* `[cut] L.STAGE1: 2 conjunct(s)`
* `[cut] L.STAGE2: 2 conjunct(s)`
* `[cut] L.STAGE3: 2 conjunct(s)`
* `[cut] L.TOPOFF: 2 conjunct(s)`
* `[cut] L.COMPLETE: 1 conjunct(s)`
* `[cut] L.ABORT: 1 conjunct(s)`
* `[cut] R.STAGE1: 2 conjunct(s)`
* `[cut] R.STAGE2: 2 conjunct(s)`
* `[cut] R.STAGE3: 2 conjunct(s)`
* `[cut] R.TOPOFF: 2 conjunct(s)`
* `[cut] R.COMPLETE: 1 conjunct(s)`
* `[cut] R.ABORT: 1 conjunct(s)`
* `[cut-x] L.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.TOPOFF: p <= 72.9 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABORT: p <= 0.5 kind=closure entry=weakening route=frozen`
* `[cut-x] R.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.TOPOFF: p <= 70.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABORT: p <= 0.5 kind=closure entry=weakening route=frozen`
* `[admissible] STAGE1_L: [STAGE1, STAGE2, STAGE3, TOPOFF, COMPLETE]`
* `[admissible] STAGE2_L: [STAGE2, STAGE3, TOPOFF, COMPLETE]`
* `[admissible] STAGE3_L: [STAGE3, TOPOFF, COMPLETE]`
* `[admissible] TOPOFF_L: [STAGE3, TOPOFF, COMPLETE]`
* `[admissible] COMPLETE_L: [TOPOFF, COMPLETE]`
* `[admissible] ABORT_L: [STAGE1, STAGE2, STAGE3, TOPOFF, COMPLETE, ABORT]`
* `--handoff`: 12/12 checked, 12 passed, failing -, non-vacuous (116 ms)
* cover `STAGE1_L`: λ = 1, budget 1, admissible ['STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': '---'}, kinds ['base'], path modes ['COMPLETE', 'STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE1`: `STAGE1:base(B=1)`
    * from `STAGE2`: `STAGE2:base(B=1)`
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `STAGE2_L`: λ = 1, budget 1, admissible ['STAGE2', 'STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': '-dd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'STAGE2', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE2`: `STAGE2:base(B=1)`
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `STAGE3_L`: λ = 1, budget 1, admissible ['STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': '-dd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `TOPOFF_L`: λ = 1, budget 1, admissible ['STAGE3', 'TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': '-dd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': 'j--'}, kinds ['base', 'repoDyn'], path modes ['COMPLETE', 'STAGE3', 'TOPOFF'], branching 0, right-only True
    * from `STAGE3`: `STAGE3:repoDyn(B=1,preJ)->[TOPOFF@1]; TOPOFF:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `COMPLETE_L`: λ = 1, budget 1, admissible ['TOPOFF', 'COMPLETE'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['COMPLETE', 'TOPOFF'], branching 0, right-only False
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
* cover `ABORT_L`: λ = 1, budget 1, admissible ['STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF', 'COMPLETE', 'ABORT'], flags {'STAGE1': 'jdd', 'STAGE2': 'jdd', 'STAGE3': 'jdd', 'TOPOFF': 'jdd', 'COMPLETE': 'j--', 'ABORT': 'j--'}, kinds ['base'], path modes ['ABORT', 'COMPLETE', 'STAGE1', 'STAGE2', 'STAGE3', 'TOPOFF'], branching 0, right-only False
    * from `STAGE1`: `STAGE1:base(B=1)`
    * from `STAGE2`: `STAGE2:base(B=1)`
    * from `STAGE3`: `STAGE3:base(B=1)`
    * from `TOPOFF`: `TOPOFF:base(B=1)`
    * from `COMPLETE`: `COMPLETE:base(B=1)`
    * from `ABORT`: `ABORT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned STAGE1->ABORT, STAGE2->ABORT but NO_PRUNE=CERTIFIED; **M5** yes: 12/12 handoffs unsat, rows differ; **M6** yes: L.STAGE1: 2 conjunct(s); L.STAGE2: 2 conjunct(s); L.STAGE3: 2 conjunct(s); L.TOPOFF: 2 conjunct(s); L.COMPLETE: 1 conjunct(s); L.ABORT: 1 conjunct(s); R.STAGE1: 2 conjunct(s); R.STAGE2: 2 conjunct(s); R.STAGE3: 2 conjunct(s); R.TOPOFF: 2 conjunct(s); R.COMPLETE: 1 conjunct(s); R.ABORT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape; L.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape; L.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape; L.TOPOFF: p <= 72.9 kind=implied-contraction entry=rational route=shape; L.ABORT: p <= 0.5 kind=closure entry=weakening route=frozen; R.STAGE1: p <= 20 kind=implied-contraction entry=rational route=shape; R.STAGE2: p <= 40 kind=implied-contraction entry=rational route=shape; R.STAGE3: p <= 60 kind=implied-contraction entry=rational route=shape; R.TOPOFF: p <= 70.5 kind=implied-contraction entry=rational route=shape; R.ABORT: p <= 0.5 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `hydro_rejection_gatecal`

* family: Hydro unit load rejection; scenario: degraded-sensor; dims L/R 3/3; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `82f0f7624bbc`
* `relcert`: **CERTIFIED** (388 ms); `[prune] hydro_rejection_gatecal: []`; NO_PRUNE: **CERTIFIED** (382 ms); NO_CUT: **CERTIFIED** (361 ms); NO_IMPLIED_CUT: **CERTIFIED** (302 ms); NO_LINEAR_CUT: **CERTIFIED** (383 ms); domains: uniform
* `[cut] L.ONGRID: 5 conjunct(s)`
* `[cut] L.REJECT: 6 conjunct(s)`
* `[cut] R.ONGRID: 5 conjunct(s)`
* `[cut] R.REJECT: 6 conjunct(s)`
* `[admissible] ONGRID_L: [ONGRID]`
* `[admissible] REJECT_L: [REJECT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (102 ms)
* cover `ONGRID_L`: λ = 1, budget 1, admissible ['ONGRID'], flags {'ONGRID': 'j--', 'REJECT': '---'}, kinds ['base'], path modes ['ONGRID'], branching 0, right-only False
    * from `ONGRID`: `ONGRID:base(B=1)`
* cover `REJECT_L`: λ = 1, budget 1, admissible ['REJECT'], flags {'ONGRID': '---', 'REJECT': 'j--'}, kinds ['base'], path modes ['REJECT'], branching 0, right-only False
    * from `REJECT`: `REJECT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.ONGRID: 5 conjunct(s); L.REJECT: 6 conjunct(s); R.ONGRID: 5 conjunct(s); R.REJECT: 6 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_csf21_vehicle_bus`

* family: Literature; scenario: sensor-attack; dims L/R 3/3; modes L/R 6/12; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `f823904414fa`
* `relcert`: **CERTIFIED** (3282 ms); `[prune] lit_csf21_vehicle_bus: []`; NO_PRUNE: **CERTIFIED** (3291 ms); NO_CUT: **CERTIFIED** (3286 ms); NO_IMPLIED_CUT: **CERTIFIED** (3276 ms); NO_LINEAR_CUT: **CERTIFIED** (3305 ms); domains: uniform
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
* `--handoff`: 24/24 checked, 24 passed, failing -, VACUOUS (identical rows) (115 ms)
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.AccCool: 1 conjunct(s); L.AccHeat: 1 conjunct(s); L.CoastCool: 2 conjunct(s); L.CoastHeat: 2 conjunct(s); R.AccCoolA: 1 conjunct(s); R.AccCoolT: 1 conjunct(s); R.AccHeatA: 1 conjunct(s); R.AccHeatT: 1 conjunct(s); R.CoastCoolA: 2 conjunct(s); R.CoastCoolT: 2 conjunct(s); R.CoastHeatA: 2 conjunct(s); R.CoastHeatT: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_csf21_vehicle_thermo`

* family: Literature; scenario: sensor-attack; dims L/R 3/3; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `bda79666f4dc`
* `relcert`: **CERTIFIED** (1755 ms); `[prune] lit_csf21_vehicle_thermo: []`; NO_PRUNE: **CERTIFIED** (1749 ms); NO_CUT: **CERTIFIED** (1657 ms); NO_IMPLIED_CUT: **CERTIFIED** (1705 ms); NO_LINEAR_CUT: **CERTIFIED** (1733 ms); domains: uniform
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
* `--handoff`: 36/36 checked, 36 passed, failing -, VACUOUS (identical rows) (126 ms)
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

### `lit_drl_car_stop`

* family: Literature; scenario: controller-refinement; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `5caefe2c658e`
* `relcert`: **CERTIFIED** (529 ms); `[prune] lit_drl_car_stop: []`; NO_PRUNE: **CERTIFIED** (524 ms); NO_CUT: **CERTIFIED** (500 ms); NO_IMPLIED_CUT: **CERTIFIED** (521 ms); NO_LINEAR_CUT: **CERTIFIED** (441 ms); domains: uniform
* `[cut] L.Accel: 1 conjunct(s)`
* `[cut] L.Coast: 2 conjunct(s)`
* `[cut] L.Brake: 1 conjunct(s)`
* `[cut] R.Accel: 1 conjunct(s)`
* `[cut] R.Coast: 2 conjunct(s)`
* `[cut] R.Brake: 1 conjunct(s)`
* `[admissible] Accel_L: [Accel, Coast, Brake]`
* `[admissible] Coast_L: [Accel, Coast, Brake]`
* `[admissible] Brake_L: [Accel, Coast, Brake]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (105 ms)
* cover `Accel_L`: λ = 1, budget 1, admissible ['Accel', 'Coast', 'Brake'], flags {'Accel': 'j--', 'Coast': '---', 'Brake': '---'}, kinds ['base', 'hop'], path modes ['Accel', 'Brake', 'Coast'], branching 0, right-only False
    * from `Accel`: `Accel:base(B=1)`
    * from `Coast`: `Coast:hop(B=1,preJ)->[Accel@1]; Accel:base(B=1)`
    * from `Brake`: `Brake:hop(B=1,preJ)->[Accel@1]; Accel:base(B=1)`
* cover `Coast_L`: λ = 1, budget 1, admissible ['Accel', 'Coast', 'Brake'], flags {'Accel': '---', 'Coast': 'j--', 'Brake': '---'}, kinds ['base', 'hop'], path modes ['Accel', 'Brake', 'Coast'], branching 0, right-only False
    * from `Accel`: `Accel:hop(B=1,preJ)->[Coast@1]; Coast:base(B=1)`
    * from `Coast`: `Coast:base(B=1)`
    * from `Brake`: `Brake:hop(B=1,preJ)->[Coast@1]; Coast:base(B=1)`
* cover `Brake_L`: λ = 1, budget 1, admissible ['Accel', 'Coast', 'Brake'], flags {'Accel': '---', 'Coast': '---', 'Brake': 'j--'}, kinds ['base', 'hop'], path modes ['Accel', 'Brake', 'Coast'], branching 0, right-only False
    * from `Accel`: `Accel:hop(B=1,preJ)->[Brake@1]; Brake:base(B=1)`
    * from `Coast`: `Coast:hop(B=1,preJ)->[Brake@1]; Brake:base(B=1)`
    * from `Brake`: `Brake:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Accel: 1 conjunct(s); L.Coast: 2 conjunct(s); L.Brake: 1 conjunct(s); R.Accel: 1 conjunct(s); R.Coast: 2 conjunct(s); R.Brake: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_drl_lane_control`

* family: Literature; scenario: controller-refinement; dims L/R 3/3; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0e06478ae77f`
* `relcert`: **CERTIFIED** (2720 ms); `[prune] lit_drl_lane_control: []`; NO_PRUNE: **CERTIFIED** (2684 ms); NO_CUT: **CERTIFIED** (2555 ms); NO_IMPLIED_CUT: **CERTIFIED** (2700 ms); NO_LINEAR_CUT: **CERTIFIED** (2808 ms); domains: uniform
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
* `--handoff`: 36/36 checked, 36 passed, failing -, VACUOUS (identical rows) (112 ms)
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

* family: Literature; scenario: information-flow; dims L/R 2/2; modes L/R 12/12; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `19b77ecb5337`
* `relcert`: **CERTIFIED** (2338 ms); `[prune] lit_freedm_meter: []`; NO_PRUNE: **CERTIFIED** (2313 ms); NO_CUT: **CERTIFIED** (2242 ms); NO_IMPLIED_CUT: **CERTIFIED** (2338 ms); NO_LINEAR_CUT: **CERTIFIED** (2330 ms); domains: uniform
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
* `--handoff`: 144/144 checked, 144 passed, failing -, VACUOUS (identical rows) (191 ms)
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.BatD0R0: 2 conjunct(s); L.BatD0R1: 1 conjunct(s); L.BatD1R0: 1 conjunct(s); L.BatD1R1: 2 conjunct(s); L.BatD2R0: 1 conjunct(s); L.BatD2R1: 1 conjunct(s); L.GridD0R0: 2 conjunct(s); L.GridD0R1: 2 conjunct(s); L.GridD1R0: 2 conjunct(s); L.GridD1R1: 2 conjunct(s); L.GridD2R0: 2 conjunct(s); L.GridD2R1: 2 conjunct(s); R.BatD0R0: 2 conjunct(s); R.BatD0R1: 1 conjunct(s); R.BatD1R0: 1 conjunct(s); R.BatD1R1: 2 conjunct(s); R.BatD2R0: 1 conjunct(s); R.BatD2R1: 1 conjunct(s); R.GridD0R0: 2 conjunct(s); R.GridD0R1: 2 conjunct(s); R.GridD1R0: 2 conjunct(s); R.GridD1R1: 2 conjunct(s); R.GridD2R0: 2 conjunct(s); R.GridD2R1: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_girard08_robot`

* family: Literature; scenario: abstraction; dims L/R 6/2; modes L/R 6/6; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic+conj; rows identical: True; normalized md5 `7d41fd8a36e8`
* `relcert`: **CERTIFIED** (3579 ms); `[prune] lit_girard08_robot: []`; NO_PRUNE: **CERTIFIED** (3561 ms); NO_CUT: **CERTIFIED** (3433 ms); NO_IMPLIED_CUT: **CERTIFIED** (3581 ms); NO_LINEAR_CUT: **CERTIFIED** (3577 ms); domains: uniform
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
* `--handoff`: 12/12 checked, 12 passed, failing -, VACUOUS (identical rows) (76 ms)
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

### `lit_hypercert_vehicle`

* family: Literature; scenario: opacity; dims L/R 2/2; modes L/R 5/5; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `31bfd2ba89f9`
* `relcert`: **CERTIFIED** (1021 ms); `[prune] lit_hypercert_vehicle: []`; NO_PRUNE: **CERTIFIED** (1004 ms); NO_CUT: **CERTIFIED** (971 ms); NO_IMPLIED_CUT: **CERTIFIED** (1025 ms); NO_LINEAR_CUT: **CERTIFIED** (948 ms); domains: uniform
* `[cut] L.Am4: 1 conjunct(s)`
* `[cut] L.Am2: 1 conjunct(s)`
* `[cut] L.A0: 2 conjunct(s)`
* `[cut] L.Ap2: 1 conjunct(s)`
* `[cut] L.Ap4: 1 conjunct(s)`
* `[cut] R.Am4: 1 conjunct(s)`
* `[cut] R.Am2: 1 conjunct(s)`
* `[cut] R.A0: 2 conjunct(s)`
* `[cut] R.Ap2: 1 conjunct(s)`
* `[cut] R.Ap4: 1 conjunct(s)`
* `[admissible] Am4_L: [Am4, Am2, A0, Ap2, Ap4]`
* `[admissible] Am2_L: [Am4, Am2, A0, Ap2, Ap4]`
* `[admissible] A0_L: [Am4, Am2, A0, Ap2, Ap4]`
* `[admissible] Ap2_L: [Am4, Am2, A0, Ap2, Ap4]`
* `[admissible] Ap4_L: [Am4, Am2, A0, Ap2, Ap4]`
* `--handoff`: 25/25 checked, 25 passed, failing -, VACUOUS (identical rows) (75 ms)
* cover `Am4_L`: λ = 1, budget 1, admissible ['Am4', 'Am2', 'A0', 'Ap2', 'Ap4'], flags {'Am4': 'j--', 'Am2': '---', 'A0': '---', 'Ap2': '---', 'Ap4': '---'}, kinds ['base', 'hop'], path modes ['A0', 'Am2', 'Am4', 'Ap2', 'Ap4'], branching 0, right-only False
    * from `Am4`: `Am4:base(B=1)`
    * from `Am2`: `Am2:hop(B=1,preJ)->[Am4@1]; Am4:base(B=1)`
    * from `A0`: `A0:hop(B=1,preJ)->[Am4@1]; Am4:base(B=1)`
    * from `Ap2`: `Ap2:hop(B=1,preJ)->[Am4@1]; Am4:base(B=1)`
    * from `Ap4`: `Ap4:hop(B=1,preJ)->[Am4@1]; Am4:base(B=1)`
* cover `Am2_L`: λ = 1, budget 1, admissible ['Am4', 'Am2', 'A0', 'Ap2', 'Ap4'], flags {'Am4': '---', 'Am2': 'j--', 'A0': '---', 'Ap2': '---', 'Ap4': '---'}, kinds ['base', 'hop'], path modes ['A0', 'Am2', 'Am4', 'Ap2', 'Ap4'], branching 0, right-only False
    * from `Am4`: `Am4:hop(B=1,preJ)->[Am2@1]; Am2:base(B=1)`
    * from `Am2`: `Am2:base(B=1)`
    * from `A0`: `A0:hop(B=1,preJ)->[Am2@1]; Am2:base(B=1)`
    * from `Ap2`: `Ap2:hop(B=1,preJ)->[Am2@1]; Am2:base(B=1)`
    * from `Ap4`: `Ap4:hop(B=1,preJ)->[Am2@1]; Am2:base(B=1)`
* cover `A0_L`: λ = 1, budget 1, admissible ['Am4', 'Am2', 'A0', 'Ap2', 'Ap4'], flags {'Am4': '---', 'Am2': '---', 'A0': 'j--', 'Ap2': '---', 'Ap4': '---'}, kinds ['base', 'hop'], path modes ['A0', 'Am2', 'Am4', 'Ap2', 'Ap4'], branching 0, right-only False
    * from `Am4`: `Am4:hop(B=1,preJ)->[A0@1]; A0:base(B=1)`
    * from `Am2`: `Am2:hop(B=1,preJ)->[A0@1]; A0:base(B=1)`
    * from `A0`: `A0:base(B=1)`
    * from `Ap2`: `Ap2:hop(B=1,preJ)->[A0@1]; A0:base(B=1)`
    * from `Ap4`: `Ap4:hop(B=1,preJ)->[A0@1]; A0:base(B=1)`
* cover `Ap2_L`: λ = 1, budget 1, admissible ['Am4', 'Am2', 'A0', 'Ap2', 'Ap4'], flags {'Am4': '---', 'Am2': '---', 'A0': '---', 'Ap2': 'j--', 'Ap4': '---'}, kinds ['base', 'hop'], path modes ['A0', 'Am2', 'Am4', 'Ap2', 'Ap4'], branching 0, right-only False
    * from `Am4`: `Am4:hop(B=1,preJ)->[Ap2@1]; Ap2:base(B=1)`
    * from `Am2`: `Am2:hop(B=1,preJ)->[Ap2@1]; Ap2:base(B=1)`
    * from `A0`: `A0:hop(B=1,preJ)->[Ap2@1]; Ap2:base(B=1)`
    * from `Ap2`: `Ap2:base(B=1)`
    * from `Ap4`: `Ap4:hop(B=1,preJ)->[Ap2@1]; Ap2:base(B=1)`
* cover `Ap4_L`: λ = 1, budget 1, admissible ['Am4', 'Am2', 'A0', 'Ap2', 'Ap4'], flags {'Am4': '---', 'Am2': '---', 'A0': '---', 'Ap2': '---', 'Ap4': 'j--'}, kinds ['base', 'hop'], path modes ['A0', 'Am2', 'Am4', 'Ap2', 'Ap4'], branching 0, right-only False
    * from `Am4`: `Am4:hop(B=1,preJ)->[Ap4@1]; Ap4:base(B=1)`
    * from `Am2`: `Am2:hop(B=1,preJ)->[Ap4@1]; Ap4:base(B=1)`
    * from `A0`: `A0:hop(B=1,preJ)->[Ap4@1]; Ap4:base(B=1)`
    * from `Ap2`: `Ap2:hop(B=1,preJ)->[Ap4@1]; Ap4:base(B=1)`
    * from `Ap4`: `Ap4:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Am4: 1 conjunct(s); L.Am2: 1 conjunct(s); L.A0: 2 conjunct(s); L.Ap2: 1 conjunct(s); L.Ap4: 1 conjunct(s); R.Am4: 1 conjunct(s); R.Am2: 1 conjunct(s); R.A0: 2 conjunct(s); R.Ap2: 1 conjunct(s); R.Ap4: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `lit_lz21_vehicle_position`

* family: Literature; scenario: opacity; dims L/R 2/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `dadc9b527492`
* `relcert`: **CERTIFIED** (410 ms); `[prune] lit_lz21_vehicle_position: []`; NO_PRUNE: **CERTIFIED** (404 ms); NO_CUT: **CERTIFIED** (375 ms); NO_IMPLIED_CUT: **CERTIFIED** (409 ms); NO_LINEAR_CUT: **CERTIFIED** (380 ms); domains: uniform
* `[cut] L.Um: 1 conjunct(s)`
* `[cut] L.U0: 2 conjunct(s)`
* `[cut] L.Up: 1 conjunct(s)`
* `[cut] R.Um: 1 conjunct(s)`
* `[cut] R.U0: 2 conjunct(s)`
* `[cut] R.Up: 1 conjunct(s)`
* `[admissible] Um_L: [Um, U0, Up]`
* `[admissible] U0_L: [Um, U0, Up]`
* `[admissible] Up_L: [Um, U0, Up]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (67 ms)
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

* family: Literature; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/2; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `136968002dbd`
* `relcert`: **CERTIFIED** (207 ms); `[prune] lit_nahs25_salt_tank: []`; NO_PRUNE: **CERTIFIED** (132 ms); NO_CUT: **DECLINED** (210 ms); NO_IMPLIED_CUT: **DECLINED** (230 ms); NO_LINEAR_CUT: **CERTIFIED** (170 ms); domains: uniform
* `[cut] L.On: 1 conjunct(s)`
* `[cut] L.Off: 1 conjunct(s)`
* `[cut] R.On: 1 conjunct(s)`
* `[cut] R.Off: 1 conjunct(s)`
* `[cut-x] L.Off: xp <= 28.0 kind=closure entry=weakening route=frozen`
* `[cut-x] R.Off: xp <= 25.0 kind=closure entry=weakening route=frozen`
* `[admissible] On_L: [On]`
* `[admissible] Off_L: [On]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (104 ms)
* cover `On_L`: λ = 1, budget 1, admissible ['On'], flags {'On': 'j--', 'Off': 'jdd'}, kinds ['base'], path modes ['On'], branching 0, right-only False
    * from `On`: `On:base(B=1)`
* cover `Off_L`: λ = 1, budget 1, admissible ['On'], flags {'On': 'j--', 'Off': 'jdd'}, kinds ['base'], path modes ['On'], branching 0, right-only False
    * from `On`: `On:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.On: 1 conjunct(s); L.Off: 1 conjunct(s); R.On: 1 conjunct(s); R.Off: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Off: xp <= 28.0 kind=closure entry=weakening route=frozen; R.Off: xp <= 25.0 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `platoon_latency`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: degraded-network; dims L/R 3/2; modes L/R 3/2; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `b2ce758edc03`
* `relcert`: **CERTIFIED** (694 ms); `[prune] platoon_latency: [CACC->AEB]`; NO_PRUNE: **CERTIFIED** (614 ms); NO_CUT: **CERTIFIED** (660 ms); NO_IMPLIED_CUT: **CERTIFIED** (636 ms); NO_LINEAR_CUT: **CERTIFIED** (646 ms); domains: uniform
* `[cut] L.CACC_UP: 4 conjunct(s)`
* `[cut] L.CACC_DN: 4 conjunct(s)`
* `[cut] L.AEB: 2 conjunct(s)`
* `[cut] R.CACC: 4 conjunct(s)`
* `[cut] R.AEB: 2 conjunct(s)`
* `[cut-x] L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[cut-x] R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[admissible] CACC_UP_L: [CACC]`
* `[admissible] CACC_DN_L: [CACC]`
* `[admissible] AEB_L: [AEB]`
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (31 ms)
* cover `CACC_UP_L`: λ = 1, budget 1, admissible ['CACC'], flags {'CACC': 'j--', 'AEB': '---'}, kinds ['base'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:base(B=1)`
* cover `CACC_DN_L`: λ = 1, budget 1, admissible ['CACC'], flags {'CACC': 'j--', 'AEB': '---'}, kinds ['base'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:base(B=1)`
* cover `AEB_L`: λ = 1, budget 1, admissible ['AEB'], flags {'CACC': '---', 'AEB': 'j--'}, kinds ['base'], path modes ['AEB'], branching 0, right-only False
    * from `AEB`: `AEB:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED; **M5** yes: 7/7 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.CACC_UP: 4 conjunct(s); L.CACC_DN: 4 conjunct(s); L.AEB: 2 conjunct(s); R.CACC: 4 conjunct(s); R.AEB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA; R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `platoon_linkloss`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: dos-attack; dims L/R 2/2; modes L/R 3/2; εL/εR 0.2/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `890bffc4eff5`
* `relcert`: **CERTIFIED** (604 ms); `[prune] platoon_linkloss: [CACC->AEB]`; NO_PRUNE: **CERTIFIED** (567 ms); NO_CUT: **CERTIFIED** (577 ms); NO_IMPLIED_CUT: **CERTIFIED** (565 ms); NO_LINEAR_CUT: **CERTIFIED** (602 ms); domains: uniform
* `[cut] L.CACC: 4 conjunct(s)`
* `[cut] L.ACC: 4 conjunct(s)`
* `[cut] L.AEB: 2 conjunct(s)`
* `[cut] R.CACC: 4 conjunct(s)`
* `[cut] R.AEB: 2 conjunct(s)`
* `[cut-x] L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[cut-x] R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[admissible] CACC_L: [CACC]`
* `[admissible] ACC_L: [CACC]`
* `[admissible] AEB_L: [AEB]`
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (111 ms)
* cover `CACC_L`: λ = 1, budget 2, admissible ['CACC'], flags {'CACC': 'j--', 'AEB': 'j--'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cover `ACC_L`: λ = 1, budget 2, admissible ['CACC'], flags {'CACC': 'j--', 'AEB': '---'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cover `AEB_L`: λ = 1, budget 2, admissible ['AEB'], flags {'CACC': '---', 'AEB': 'j--'}, kinds ['base', 'joint'], path modes ['AEB'], branching 0, right-only False
    * from `AEB`: `AEB:joint(B=2)->[AEB@1, AEB@1]; AEB:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: CACC B=2 via CACC, ACC B=2 via CACC, AEB B=2 via AEB; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED; **M5** yes: 7/7 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.CACC: 4 conjunct(s); L.ACC: 4 conjunct(s); L.AEB: 2 conjunct(s); R.CACC: 4 conjunct(s); R.AEB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA; R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `platoon_profiles`

* family: Platoon follower (CACC: link loss, latency, profiles); scenario: controller-refinement; dims L/R 2/2; modes L/R 2/2; εL/εR 0.1/0.1; λ ∈ [1.0, 1.2]; invariant shape conjunctive; rows identical: False; normalized md5 `68f4c3493847`
* `relcert`: **CERTIFIED** (2270 ms); `[prune] platoon_profiles: [CACC->AEB]`; NO_PRUNE: **CERTIFIED** (2289 ms); NO_CUT: **CERTIFIED** (3417 ms); NO_IMPLIED_CUT: **CERTIFIED** (2522 ms); NO_LINEAR_CUT: **CERTIFIED** (2268 ms); domains: uniform
* `[cut] L.SPORT: 4 conjunct(s)`
* `[cut] L.AEB: 2 conjunct(s)`
* `[cut] R.CACC: 4 conjunct(s)`
* `[cut] R.AEB: 2 conjunct(s)`
* `[cut-x] L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[cut-x] R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA`
* `[admissible] SPORT_L: [CACC]`
* `[admissible] AEB_L: [AEB]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (108 ms)
* cover `SPORT_L`: λ = 6/5, budget 2, admissible ['CACC'], flags {'CACC': 'j--', 'AEB': '---'}, kinds ['base', 'joint'], path modes ['CACC'], branching 0, right-only False
    * from `CACC`: `CACC:joint(B=2)->[CACC@1, CACC@1]; CACC:base(B=1)`
* cover `AEB_L`: λ = 1, budget 1, admissible ['AEB'], flags {'CACC': '---', 'AEB': 'j--'}, kinds ['base'], path modes ['AEB'], branching 0, right-only False
    * from `AEB`: `AEB:base(B=1)`
* cells: **M1** yes: SPORT λ=6/5 (affine dynamics); **M2** yes: SPORT B=2 via CACC; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CACC->AEB but NO_PRUNE=CERTIFIED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.SPORT: 4 conjunct(s); L.AEB: 2 conjunct(s); R.CACC: 4 conjunct(s); R.AEB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA; R.AEB: (g + (2.0 * r)) <= 5.0 kind=closure entry=weakening route=diA) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `quad_light_lag`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 3/3; modes L/R 1/1; εL/εR 1.0/1.0; λ ∈ [1.2, 1.2]; invariant shape conjunctive; rows identical: True; normalized md5 `6643174d6134`
* `relcert`: **CERTIFIED** (187 ms); `[prune] quad_light_lag: []`; NO_PRUNE: **CERTIFIED** (148 ms); NO_CUT: **CERTIFIED** (123 ms); NO_IMPLIED_CUT: **CERTIFIED** (170 ms); NO_LINEAR_CUT: **CERTIFIED** (167 ms); domains: uniform
* `[cut] L.CLIMB: 3 conjunct(s)`
* `[cut] R.CLIMB: 3 conjunct(s)`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (84 ms)
* cover `CLIMB_L`: λ = 6/5, budget 2, admissible ['CLIMB'], flags {'CLIMB': 'j--'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=6/5 (affine dynamics); **M2** yes: CLIMB B=2 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 3 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `quad_light_profiles`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 2/2; modes L/R 1/3; εL/εR 1.0/1.0; λ ∈ [1.2, 1.2]; invariant shape conjunctive; rows identical: True; normalized md5 `588769663a15`
* `relcert`: **CERTIFIED** (282 ms); `[prune] quad_light_profiles: []`; NO_PRUNE: **CERTIFIED** (273 ms); NO_CUT: **CERTIFIED** (270 ms); NO_IMPLIED_CUT: **CERTIFIED** (205 ms); NO_LINEAR_CUT: **CERTIFIED** (247 ms); domains: uniform
* `[cut] L.CLIMB: 2 conjunct(s)`
* `[cut] R.NORMAL: 3 conjunct(s)`
* `[cut] R.ECO: 3 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[admissible] CLIMB_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (67 ms)
* cover `CLIMB_L`: λ = 6/5, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': '---', 'SPORT': '---'}, kinds ['base', 'hop', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `ECO`: `ECO:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
    * from `SPORT`: `SPORT:hop(B=2,preJ)->[NORMAL@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:hop(B=1,postJ)->[NORMAL@1]; SPORT:hop(B=1,postJ)->[NORMAL@1]`
* cells: **M1** yes: CLIMB λ=6/5 (affine dynamics); **M2** yes: CLIMB B=2 via NORMAL +choice ECO:hop/SPORT:hop; **M3** yes: CLIMB branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.NORMAL: 3 conjunct(s); R.ECO: 3 conjunct(s); R.SPORT: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `reactor_feed_wireless`

* family: Exothermic reactor feed interlock; scenario: degraded-sensor; dims L/R 2/2; modes L/R 4/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `2ea3ed4ab4bb`
* `relcert`: **CERTIFIED** (757 ms); `[prune] reactor_feed_wireless: [F1->F4, F2->F4, F3->F1, F4->F1]`; NO_PRUNE: **DECLINED** (304 ms); NO_CUT: **CERTIFIED** (659 ms); NO_IMPLIED_CUT: **CERTIFIED** (710 ms); NO_LINEAR_CUT: **CERTIFIED** (788 ms); domains: uniform
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
* `--handoff`: 16/16 checked, 16 passed, failing -, VACUOUS (identical rows) (102 ms)
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

* family: Rover ladder; scenario: model-refinement; dims L/R 3/3; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `2c6f0b416f13`
* `relcert`: **CERTIFIED** (408 ms); `[prune] rover_ladder_2to3: []`; NO_PRUNE: **CERTIFIED** (422 ms); NO_CUT: **CERTIFIED** (319 ms); NO_IMPLIED_CUT: **CERTIFIED** (322 ms); NO_LINEAR_CUT: **CERTIFIED** (404 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (39 ms)
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

* family: Rover ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `13c4ddc72a8e`
* `relcert`: **CERTIFIED** (727 ms); `[prune] rover_ladder_3to6: []`; NO_PRUNE: **CERTIFIED** (790 ms); NO_CUT: **CERTIFIED** (689 ms); NO_IMPLIED_CUT: **CERTIFIED** (729 ms); NO_LINEAR_CUT: **CERTIFIED** (750 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (98 ms)
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

* family: Rover ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.25]; invariant shape quadratic+conj; rows identical: True; normalized md5 `1f6d1ddc8837`
* `relcert`: **CERTIFIED** (17191 ms); `[prune] rover_ladder_6to8: []`; NO_PRUNE: **CERTIFIED** (17197 ms); NO_CUT: **DECLINED** (13687 ms); NO_IMPLIED_CUT: **CERTIFIED** (17202 ms); NO_LINEAR_CUT: **CERTIFIED** (17260 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (66 ms)
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

* family: Rover ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.25]; invariant shape quadratic+conj; rows identical: True; normalized md5 `218a65bb5a5f`
* `relcert`: **CERTIFIED** (31277 ms); `[prune] rover_ladder_8to12: []`; NO_PRUNE: **CERTIFIED** (31216 ms); NO_CUT: **DECLINED** (31377 ms); NO_IMPLIED_CUT: **CERTIFIED** (31120 ms); NO_LINEAR_CUT: **CERTIFIED** (31151 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (72 ms)
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

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/2; modes L/R 4/4; εL/εR 1.0/1.0; λ ∈ [1.0, 1.5]; invariant shape conjunctive; rows identical: True; normalized md5 `4d8452f7b361`
* `relcert`: **CERTIFIED** (1254 ms); `[prune] rover_patrol_lag: []`; NO_PRUNE: **CERTIFIED** (1220 ms); NO_CUT: **CERTIFIED** (1740 ms); NO_IMPLIED_CUT: **CERTIFIED** (1205 ms); NO_LINEAR_CUT: **CERTIFIED** (1298 ms); domains: uniform
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
* `--handoff`: 10/10 checked, 10 passed, failing -, VACUOUS (identical rows) (111 ms)
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

* family: Terrain chain; scenario: model-refinement; dims L/R 4/4; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 3.0]; invariant shape conjunctive; rows identical: True; normalized md5 `efe2e0279e7d`
* `relcert`: **CERTIFIED** (2215 ms); `[prune] rover_terrain_2to4: []`; NO_PRUNE: **CERTIFIED** (2215 ms); NO_CUT: **DECLINED** (2501 ms); NO_IMPLIED_CUT: **CERTIFIED** (2182 ms); NO_LINEAR_CUT: **CERTIFIED** (2216 ms); domains: uniform
* `[cut] L.MUD: 2 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 1 conjunct(s)`
* `[cut] R.GRAVEL: 1 conjunct(s)`
* `[cut] R.PAVED: 1 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (1076 ms)
* cover `MUD_L`: λ = 1, budget 1, admissible ['MUD', 'GRAVEL', 'PAVED'], flags {'MUD': 'j--', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base'], path modes ['GRAVEL', 'MUD', 'PAVED'], branching 0, right-only False
    * from `MUD`: `MUD:base(B=1)`
    * from `GRAVEL`: `GRAVEL:base(B=1)`
    * from `PAVED`: `PAVED:base(B=1)`
* cover `GRAVEL_L`: λ = 13/10, budget 2, admissible ['GRAVEL', 'PAVED'], flags {'MUD': '---', 'GRAVEL': 'j--', 'PAVED': 'j--'}, kinds ['base', 'joint'], path modes ['GRAVEL', 'PAVED'], branching 1, right-only False
    * from `GRAVEL`: `GRAVEL:joint(B=2)->[GRAVEL@1, PAVED@1, GRAVEL@1]; GRAVEL:base(B=1); PAVED:base(B=1)`
    * from `PAVED`: `PAVED:joint(B=2)->[PAVED@1, PAVED@1]; PAVED:base(B=1)`
* cover `PAVED_L`: λ = 27/10, budget 3, admissible ['PAVED'], flags {'MUD': '---', 'GRAVEL': '---', 'PAVED': 'j--'}, kinds ['base', 'joint'], path modes ['PAVED'], branching 0, right-only False
    * from `PAVED`: `PAVED:joint(B=3)->[PAVED@2, PAVED@2]; PAVED:joint(B=2)->[PAVED@1, PAVED@1]; PAVED:base(B=1)`
* cells: **M1** yes: GRAVEL λ=13/10, PAVED λ=27/10 (affine dynamics); **M2** yes: GRAVEL B=2 via GRAVEL/PAVED, PAVED B=3 via PAVED; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.MUD: 2 conjunct(s); L.GRAVEL: 2 conjunct(s); L.PAVED: 2 conjunct(s); R.MUD: 1 conjunct(s); R.GRAVEL: 1 conjunct(s); R.PAVED: 1 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_terrain_4to6`

* family: Terrain chain; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `83e9b7f542da`
* `relcert`: **CERTIFIED** (1117 ms); `[prune] rover_terrain_4to6: []`; NO_PRUNE: **CERTIFIED** (1034 ms); NO_CUT: **DECLINED** (478 ms); NO_IMPLIED_CUT: **CERTIFIED** (1085 ms); NO_LINEAR_CUT: **CERTIFIED** (1113 ms); domains: uniform
* `[cut] L.MUD: 2 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 2 conjunct(s)`
* `[cut] R.GRAVEL: 2 conjunct(s)`
* `[cut] R.PAVED: 2 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (24 ms)
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

* family: Terrain chain; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9c16c46c52c4`
* `relcert`: **CERTIFIED** (2099 ms); `[prune] rover_terrain_6to12: []`; NO_PRUNE: **CERTIFIED** (2115 ms); NO_CUT: **DECLINED** (905 ms); NO_IMPLIED_CUT: **CERTIFIED** (2099 ms); NO_LINEAR_CUT: **CERTIFIED** (2132 ms); domains: uniform
* `[cut] L.MUD: 3 conjunct(s)`
* `[cut] L.GRAVEL: 2 conjunct(s)`
* `[cut] L.PAVED: 2 conjunct(s)`
* `[cut] R.MUD: 2 conjunct(s)`
* `[cut] R.GRAVEL: 2 conjunct(s)`
* `[cut] R.PAVED: 2 conjunct(s)`
* `[admissible] MUD_L: [MUD, GRAVEL, PAVED]`
* `[admissible] GRAVEL_L: [GRAVEL, PAVED]`
* `[admissible] PAVED_L: [PAVED]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (26 ms)
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

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 6/6; modes L/R 2/3; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `0a029c05c972`
* `relcert`: **CERTIFIED** (2790 ms); `[prune] sat3w_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **CERTIFIED** (2817 ms); NO_CUT: **DECLINED** (1499 ms); NO_IMPLIED_CUT: **CERTIFIED** (2652 ms); NO_LINEAR_CUT: **CERTIFIED** (2829 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.FINE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE, FINE]`
* `[admissible] FINE_L: [DETUMBLE, FINE]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (29 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': 'j--', 'FINE': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
    * from `FINE`: `FINE:hop(B=2,preJ)->[DETUMBLE@2]; DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': '---', 'FINE': 'j--', 'SAFE': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:hop(B=2,preJ)->[FINE@2]; FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
    * from `FINE`: `FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE +choice DETUMBLE:hop; **M3** no (max non-self successors at a joint step = 1); **M4** vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.FINE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_phases`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 4/4; modes L/R 2/3; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `fde97f17e55a`
* `relcert`: **CERTIFIED** (4603 ms); `[prune] sat_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **CERTIFIED** (4551 ms); NO_CUT: **DECLINED** (2354 ms); NO_IMPLIED_CUT: **CERTIFIED** (4377 ms); NO_LINEAR_CUT: **CERTIFIED** (4592 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.FINE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE, FINE]`
* `[admissible] FINE_L: [DETUMBLE, FINE]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': 'j--', 'FINE': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
    * from `FINE`: `FINE:hop(B=2,preJ)->[DETUMBLE@2]; DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1, FINE@1]; DETUMBLE:base(B=1); FINE:hop(B=1,postJ)->[DETUMBLE@1]`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE', 'FINE'], flags {'DETUMBLE': '---', 'FINE': 'j--', 'SAFE': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['DETUMBLE', 'FINE'], branching 1, right-only False
    * from `DETUMBLE`: `DETUMBLE:hop(B=2,preJ)->[FINE@2]; FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
    * from `FINE`: `FINE:joint(B=2)->[FINE@1, FINE@1, DETUMBLE@1]; FINE:base(B=1); DETUMBLE:hop(B=1,postJ)->[FINE@1]`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE +choice FINE:hop, FINE B=2 via FINE +choice DETUMBLE:hop; **M3** no (max non-self successors at a joint step = 1); **M4** vacuous: pruned DETUMBLE->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.FINE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_weak`

* family: Rigid-body detumbling (polynomial); scenario: degraded-actuator; dims L/R 4/4; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [0.8, 0.8]; invariant shape quadratic; rows identical: True; normalized md5 `276c5ab9d159`
* `relcert`: **CERTIFIED** (2011 ms); `[prune] sat_detumble_weak: [NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE]`; NO_PRUNE: **CERTIFIED** (2016 ms); NO_CUT: **CERTIFIED** (1890 ms); NO_IMPLIED_CUT: **CERTIFIED** (1986 ms); NO_LINEAR_CUT: **CERTIFIED** (1941 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.NOMINAL: 1 conjunct(s)`
* `[cut] R.ECONOMY: 1 conjunct(s)`
* `[cut] R.SURVIVAL: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [NOMINAL, ECONOMY, SURVIVAL]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (90 ms)
* cover `DETUMBLE_L`: λ = 4/5, budget 2, admissible ['NOMINAL', 'ECONOMY', 'SURVIVAL'], flags {'NOMINAL': 'j--', 'ECONOMY': '---', 'SURVIVAL': '---', 'SAFE': '---'}, kinds ['base', 'hop', 'joint'], path modes ['ECONOMY', 'NOMINAL', 'SURVIVAL'], branching 2, right-only False
    * from `NOMINAL`: `NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
    * from `ECONOMY`: `ECONOMY:hop(B=2,preJ)->[NOMINAL@2]; NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
    * from `SURVIVAL`: `SURVIVAL:hop(B=2,preJ)->[NOMINAL@2]; NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:hop(B=1,postJ)->[NOMINAL@1]; SURVIVAL:hop(B=1,postJ)->[NOMINAL@1]`
* cells: **M1** yes: DETUMBLE λ=4/5 (affine dynamics); **M2** yes: DETUMBLE B=2 via NOMINAL +choice ECONOMY:hop/SURVIVAL:hop; **M3** yes: DETUMBLE branch=2; **M4** vacuous: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY: 1 conjunct(s); R.SURVIVAL: 1 conjunct(s); R.SAFE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `syringe_relay_prearm`

* family: Syringe-pump relay; scenario: controller-change; dims L/R 4/4; modes L/R 6/4; εL/εR 0.1/0.1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `1d16789caafc`
* `relcert`: **CERTIFIED** (1208 ms); `[prune] syringe_relay_prearm: []`; NO_PRUNE: **CERTIFIED** (1123 ms); NO_CUT: **CERTIFIED** (1397 ms); NO_IMPLIED_CUT: **CERTIFIED** (1066 ms); NO_LINEAR_CUT: **CERTIFIED** (1122 ms); domains: uniform
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
* `--handoff`: 13/13 checked, 13 passed, failing -, non-vacuous (100 ms)
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
* `relcert`: **CERTIFIED** (972 ms); `[prune] tank_dos_3to1: []`; NO_PRUNE: **CERTIFIED** (912 ms); NO_CUT: **DECLINED** (301 ms); NO_IMPLIED_CUT: **CERTIFIED** (910 ms); NO_LINEAR_CUT: **CERTIFIED** (956 ms); domains: uniform
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
* `--handoff`: 10/10 checked, 10 passed, failing -, VACUOUS (identical rows) (83 ms)
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
* `relcert`: **CERTIFIED** (2287 ms); `[prune] train_ato_odometry: []`; NO_PRUNE: **CERTIFIED** (2356 ms); NO_CUT: **CERTIFIED** (2256 ms); NO_IMPLIED_CUT: **CERTIFIED** (2274 ms); NO_LINEAR_CUT: **CERTIFIED** (2291 ms); domains: uniform
* `[cut] L.PL1: 2 conjunct(s)`
* `[cut] L.PL2: 2 conjunct(s)`
* `[cut] L.PL3: 2 conjunct(s)`
* `[cut] R.PL1: 2 conjunct(s)`
* `[cut] R.PL2: 2 conjunct(s)`
* `[cut] R.PL3: 2 conjunct(s)`
* `[admissible] PL1_L: [PL1, PL2, PL3]`
* `[admissible] PL2_L: [PL1, PL2, PL3]`
* `[admissible] PL3_L: [PL1, PL2, PL3]`
* `--handoff`: 9/9 checked, 9 passed, failing -, VACUOUS (identical rows) (107 ms)
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

### `tunnel_jetfan_pairout`

* family: Road-tunnel ventilation through a fire alarm; scenario: degraded-actuator; dims L/R 3/3; modes L/R 2/2; εL/εR 1/1; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `494352c1f894`
* `relcert`: **CERTIFIED** (330 ms); `[prune] tunnel_jetfan_pairout: []`; NO_PRUNE: **CERTIFIED** (279 ms); NO_CUT: **DECLINED** (244 ms); NO_IMPLIED_CUT: **CERTIFIED** (293 ms); NO_LINEAR_CUT: **CERTIFIED** (288 ms); domains: uniform
* `[cut] L.NORMAL: 6 conjunct(s)`
* `[cut] L.FIRE: 6 conjunct(s)`
* `[cut] R.NORMAL: 6 conjunct(s)`
* `[cut] R.FIRE: 6 conjunct(s)`
* `[admissible] NORMAL_L: [NORMAL]`
* `[admissible] FIRE_L: [FIRE]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (82 ms)
* cover `NORMAL_L`: λ = 1, budget 1, admissible ['NORMAL'], flags {'NORMAL': 'j--', 'FIRE': '---'}, kinds ['base'], path modes ['NORMAL'], branching 0, right-only False
    * from `NORMAL`: `NORMAL:base(B=1)`
* cover `FIRE_L`: λ = 1, budget 1, admissible ['FIRE'], flags {'NORMAL': '---', 'FIRE': 'j--'}, kinds ['base'], path modes ['FIRE'], branching 0, right-only False
    * from `FIRE`: `FIRE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.NORMAL: 6 conjunct(s); L.FIRE: 6 conjunct(s); R.NORMAL: 6 conjunct(s); R.FIRE: 6 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `turbine_startup_gearratio`

* family: Wind turbine start-up; scenario: degraded-controller (configuration error after a gearbox exchange); dims L/R 1/1; modes L/R 4/4; εL/εR 1.0/1.0; λ ∈ [1.0, 1.0]; invariant shape linear; rows identical: True; normalized md5 `faca661f3321`
* `relcert`: **CERTIFIED** (322 ms); `[prune] turbine_startup_gearratio: [SPINUP->STOP, RAMP->STOP]`; NO_PRUNE: **DECLINED** (197 ms); NO_CUT: **DECLINED** (148 ms); NO_IMPLIED_CUT: **DECLINED** (148 ms); NO_LINEAR_CUT: **CERTIFIED** (399 ms); domains: uniform
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
* `--handoff`: 8/8 checked, 8 passed, failing -, VACUOUS (identical rows) (94 ms)
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

* family: Volume-controlled ventilation; scenario: degraded-actuator; dims L/R 2/2; modes L/R 2/2; εL/εR 0.01/0.01; λ ∈ [1.0, 1.0]; invariant shape conjunctive; rows identical: False; normalized md5 `aee146c73337`
* `relcert`: **CERTIFIED** (274 ms); `[prune] ventilator_vc_cuffleak: []`; NO_PRUNE: **CERTIFIED** (221 ms); NO_CUT: **CERTIFIED** (231 ms); NO_IMPLIED_CUT: **CERTIFIED** (267 ms); NO_LINEAR_CUT: **CERTIFIED** (291 ms); domains: uniform
* `[cut] L.INSP: 3 conjunct(s)`
* `[cut] L.EXP: 5 conjunct(s)`
* `[cut] R.INSP: 3 conjunct(s)`
* `[cut] R.EXP: 5 conjunct(s)`
* `[admissible] INSP_L: [INSP]`
* `[admissible] EXP_L: [EXP]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (76 ms)
* cover `INSP_L`: λ = 1, budget 1, admissible ['INSP'], flags {'INSP': 'j--', 'EXP': '---'}, kinds ['base'], path modes ['INSP'], branching 0, right-only False
    * from `INSP`: `INSP:base(B=1)`
* cover `EXP_L`: λ = 1, budget 1, admissible ['EXP'], flags {'INSP': '---', 'EXP': 'j--'}, kinds ['base'], path modes ['EXP'], branching 0, right-only False
    * from `EXP`: `EXP:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 3/3 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.INSP: 3 conjunct(s); L.EXP: 5 conjunct(s); R.INSP: 3 conjunct(s); R.EXP: 5 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `watertank`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/5; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a7fe649fff6c`
* `relcert`: **CERTIFIED** (687 ms); `[prune] watertank: [Low->PumpOff]`; NO_PRUNE: **CERTIFIED** (1432 ms); NO_CUT: **CERTIFIED** (2294 ms); NO_IMPLIED_CUT: **CERTIFIED** (2539 ms); NO_LINEAR_CUT: **CERTIFIED** (631 ms); domains: uniform
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
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (104 ms)
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

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/6; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `3cd19c92e26e`
* `relcert`: **CERTIFIED** (1865 ms); `[prune] watertank_twospeed: [Fast->PumpOff]`; NO_PRUNE: **DECLINED** (1525 ms); NO_CUT: **CERTIFIED** (2715 ms); NO_IMPLIED_CUT: **CERTIFIED** (3062 ms); NO_LINEAR_CUT: **CERTIFIED** (1863 ms); domains: uniform
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
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (58 ms)
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
* cells: **M1** yes: Low λ=2 (per pairing: {'Fast': '1', 'MidEco': '3/2', 'MidBoost': '1', 'High': '1'}), Mid λ=2 (affine dynamics); **M2** yes: Low B=2 via Fast/MidBoost/MidEco/Slow, Mid B=2 via High/MidBoost/MidEco; **M3** yes: Low branch=3, Mid branch=2; **M4** yes: pruned Fast->PumpOff; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.High: 1 conjunct(s); R.Fast: 2 conjunct(s); R.Slow: 2 conjunct(s); R.MidEco: 2 conjunct(s); R.MidBoost: 2 conjunct(s); R.High: 1 conjunct(s); R.PumpOff: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape; L.Mid: x <= 20.0 kind=closure entry=weakening route=shape; R.Fast: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.Slow: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape; R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape; R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `zone_lightmass_schedule`

* family: Building zone heating (lightweight construction); scenario: model-refinement; dims L/R 1/1; modes L/R 2/3; εL/εR 5.0/5.0; λ ∈ [2.0, 2.0]; invariant shape conjunctive; rows identical: True; normalized md5 `dee0ceb952d7`
* `relcert`: **CERTIFIED** (253 ms); `[prune] zone_lightmass_schedule: []`; NO_PRUNE: **CERTIFIED** (223 ms); NO_CUT: **CERTIFIED** (222 ms); NO_IMPLIED_CUT: **CERTIFIED** (136 ms); NO_LINEAR_CUT: **CERTIFIED** (243 ms); domains: uniform
* `[cut] L.COMFORT: 2 conjunct(s)`
* `[cut] L.ECONOMY: 2 conjunct(s)`
* `[cut] R.COMFORT: 2 conjunct(s)`
* `[cut] R.STANDBY: 2 conjunct(s)`
* `[cut] R.ECONOMY: 2 conjunct(s)`
* `[admissible] COMFORT_L: [COMFORT, STANDBY, ECONOMY]`
* `[admissible] ECONOMY_L: [COMFORT, STANDBY, ECONOMY]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `COMFORT_L`: λ = 2, budget 2, admissible ['COMFORT', 'STANDBY', 'ECONOMY'], flags {'COMFORT': 'j--', 'STANDBY': '---', 'ECONOMY': '---'}, kinds ['base', 'hop', 'joint'], path modes ['COMFORT', 'ECONOMY', 'STANDBY'], branching 2, right-only False
    * from `COMFORT`: `COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, STANDBY@1, ECONOMY@1]; COMFORT:base(B=1); STANDBY:hop(B=1,postJ)->[COMFORT@1]; ECONOMY:hop(B=1,postJ)->[COMFORT@1]`
    * from `STANDBY`: `STANDBY:hop(B=2,preJ)->[COMFORT@2]; COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, STANDBY@1, ECONOMY@1]; COMFORT:base(B=1); STANDBY:hop(B=1,postJ)->[COMFORT@1]; ECONOMY:hop(B=1,postJ)->[COMFORT@1]`
    * from `ECONOMY`: `ECONOMY:hop(B=2,preJ)->[COMFORT@2]; COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, STANDBY@1, ECONOMY@1]; COMFORT:base(B=1); STANDBY:hop(B=1,postJ)->[COMFORT@1]; ECONOMY:hop(B=1,postJ)->[COMFORT@1]`
* cover `ECONOMY_L`: λ = 2, budget 2, admissible ['COMFORT', 'STANDBY', 'ECONOMY'], flags {'COMFORT': '---', 'STANDBY': '---', 'ECONOMY': 'j--'}, kinds ['base', 'hop', 'joint'], path modes ['COMFORT', 'ECONOMY', 'STANDBY'], branching 2, right-only False
    * from `COMFORT`: `COMFORT:hop(B=2,preJ)->[ECONOMY@2]; ECONOMY:joint(B=2)->[ECONOMY@1, ECONOMY@1, COMFORT@1, STANDBY@1]; ECONOMY:base(B=1); COMFORT:hop(B=1,postJ)->[ECONOMY@1]; STANDBY:hop(B=1,postJ)->[ECONOMY@1]`
    * from `STANDBY`: `STANDBY:hop(B=2,preJ)->[ECONOMY@2]; ECONOMY:joint(B=2)->[ECONOMY@1, ECONOMY@1, COMFORT@1, STANDBY@1]; ECONOMY:base(B=1); COMFORT:hop(B=1,postJ)->[ECONOMY@1]; STANDBY:hop(B=1,postJ)->[ECONOMY@1]`
    * from `ECONOMY`: `ECONOMY:joint(B=2)->[ECONOMY@1, ECONOMY@1, COMFORT@1, STANDBY@1]; ECONOMY:base(B=1); COMFORT:hop(B=1,postJ)->[ECONOMY@1]; STANDBY:hop(B=1,postJ)->[ECONOMY@1]`
* cells: **M1** yes: COMFORT λ=2, ECONOMY λ=2 (affine dynamics); **M2** yes: COMFORT B=2 via COMFORT +choice ECONOMY:hop/STANDBY:hop, ECONOMY B=2 via ECONOMY +choice COMFORT:hop/STANDBY:hop; **M3** yes: COMFORT branch=2, ECONOMY branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.COMFORT: 2 conjunct(s); L.ECONOMY: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.STANDBY: 2 conjunct(s); R.ECONOMY: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

