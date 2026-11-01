# The stop-line rover ladder: design note for review (2026-11-01)

Status: a proposal installed on branch `claude/brave-albattani-ylktc0` (batch I12) for the owner's review; not
approved. It replaces the rover refinement ladder (`rover_ladder_{2to3,3to6,6to8,8to12}`, now in
`benchmarks/reserve/`). This note collects what the rung headers do not: the stretch variant scoped after
installation, the check against the agreed requirements, the open gaps, and the fallback design.

## The ladder as installed

Files: `benchmarks/suite_v2/stopline_rover_{2to5,5to8,8to11,11to15}/input.txt` (each header states the full
system). Level names count state variables (not mechanical degrees of freedom).

Setting. A rover approaches a stop line on a level, straight corridor at up to 8 m/s; decisions every 0.1 s on
both sides from the wheel odometer p and the speed v. Modes on every level: CRUISE (p < 100, v >= 0.35, speed
held), BRAKE (p >= 100, v >= 0.35), STOP (p >= 100, v <= 0.35, frozen). Along-track position s loses progress to
heading and crabbing, so s <= p.

Safety margin. The planner's point model L2 brakes at 3 m/s^2; its stop point P* = p + v^2/6 stays 5 m short of
the line (110.67 m against 115.67 m at 8 m/s).

| rung | left / right | added physics | loss row (BRAKE, STOP) | loss delta | edge |
|---|---|---|---|---|---|
| `2to5` | L5 (p, s, v, b, psi) / L2 (p, v) | brake actuator lag 0.3 s; heading | Z5(L) <= Z2(R) + 2.4 | 2.4 m = tau V | 2.398 declines |
| `5to8` | L8 / L5 | friction-limited deceleration 2.7 m/s^2 (gravel, mu 0.275); pitch, heave, roll (brake pitch 0.02 rad per m/s^2) | Z8(L) <= Z5(R) + 1.185 | (V^2/2a)(1/kappa - 1) | 1.181 declines |
| `8to11` | L11 / L8 | tyre relaxation lag 0.05 s behind hub pressure c; yaw and pitch inertia | Z11(L) <= Z8(R) + 0.4 | 0.05 V | 0.398 declines |
| `11to15` | L15 / L11 | aerodynamic and rolling drag; heave and roll inertia; tyre slip y | Z11(L) <= Z11(R) + 0 | 0 (drag only shortens) | -0.05 declines; needs b, c <= 2.7 |

Stop-point functionals (conserved by each level's braking flow, non-increasing on L15): Z2 = p + v^2/6;
Z5 = p + 0.3 v + (v - 0.3 b)^2/6; Z8 = p + 0.3 v + (v - 0.3 b)^2/5.4; Z11 = p + 0.35 v - 0.015 b +
(v - 0.05 b - 0.3 c)^2/5.4. CRUISE rows on every rung: p_L = p_R, v_L = v_R, brake states 0 (both sides trigger at
the same decision). Every rung also carries the left level's attitude requirement rows (heading 0.35, pitch 0.25,
roll 0.2, LTR 0.8, lane 0.25; tightest values in the headers) and s_L <= p_L.

Composition. Each right model is the previous left verbatim: Z15 <= Z11 <= Z8 + 0.4 <= Z5 + 1.585 <= P* + 3.985;
the L15 rover stands still within P* + 4.03 m (standstill residual 0.04 m), 0.97 m of the 5 m margin left.
Simulation at 8 m/s (script below): standstill odometer 110.66 (L2), 112.93, 114.13, 114.51, 112.98 m (L15),
along-track 112.74 m; chain bound 114.66 m.

Measured (2026-11-01, `RELCERT_IMPLIED_CUT=1`): all four CERTIFIED (0.9, 1.8, 3.8, 7.2 s) and under every
counter-run (SYNC, NO_PRUNE, NO_CHOICE, NO_PRUNE+NO_CHOICE, NO_CUT, NO_REPO, OPREGION, WELLFORMED_STRICT);
`--handoff` 5/5 each; `--wellformed` strict 12/12 right modes ok. Letters: D on each rung (mode-dependent rows).
Assumption 1: one shared lemma `Proofs/Encoding/WellFormedStopline.lean` plus four instance proofs. The records
are emitted with `RELCERT_NO_REPO=1` (`scripts/gen_v2_data.py`, `NO_REPO_EMIT`): the default cover's right-only
reposition has a two-stage progress certificate (one stage up, one down) that the bridge's progress lemmas do not
cover; the joint-step cover certifies too.

## Scoped after installation, not installed: a stretch on the friction rung (S)

Add to the BRAKE row of `stopline_rover_5to8` only, and set `lambda_min = 0.9`, `lambda_max = 1.0`:

    (<= L_v R_v) (>= L_b (* 0.9 R_b))

Meaning: while braking, the refined rover's speed stays at or below the plan's speed profile slowed by 0.9, so its
braking takes at most 1/0.9 of the plan's (a time-to-stop requirement beside the stop-distance loss). The second
row is the inductive helper (the derated brake reaches 2.7 faster than the re-timed plan's brake reaches 0.9 of 3).

| variant | default | SYNC |
|---|---|---|
| speed row only | DECLINED | DECLINED |
| speed row + helper, BRAKE only | CERTIFIED | DECLINED |
| the same rows also in STOP | DECLINED | DECLINED (a stopped rover may creep faster than the plan) |

Edge: a single pinned lambda declines at every value (CRUISE and STOP need 1); with a range, BRAKE certifies at
0.9 and below and declines from 0.905: 0.9 = 2.7/3, the friction ratio, is the tightest. Budget 1 on every node
(no M). The tyre rung does not take a stretch (three helper variants decline, default and SYNC): both sides target
2.7 and the extra lag is a delay, which no stretch below 1 absorbs. By the same reasoning (not measured) the lag
rung is a delay and the drag rung certifies at lambda 1 (no S).

## Check against the agreed requirements

| requirement | status |
|---|---|
| 4 composing rungs, safety margin and potential safety loss, zero-loss rungs allowed | met |
| relational property (not considered otherwise) | met for the CRUISE equalities, the loss rows and the scoped time-to-stop row; NOT for the attitude rows, which bound the left only |
| certifies under the default recipe and the strict two-clause well-formedness gate | met |
| physically realistic with sources | not yet: brake lag 0.3 s, gravel mu 0.275, tyre relaxation 0.4 m, C_dA 1.5 m^2, brake pitch 0.02 rad per m/s^2 are typical values without citations |
| published cases | not required for this series (owner, 2026-11-01) |
| letters from the claim's form disclosed in the header | pending: S (scoped) would come from the time-to-stop claim |
| mechanisms judged per group | weak: D (plus S if the stretch is added); the old ladder showed S M I on two rungs |
| never tune a constant to trigger a letter | met: closed-form losses; 0.9 is the friction ratio |
| parameter windows away from decline edges | not met as written: every delta and the 0.9 stretch sit at their edge; either state them as tightest values or certify looser constants (e.g. 2.5, 1.2, 0.45, 0.05, still inside the 5 m margin) |
| terrain chain kept as the second chain | met (untouched) |

## Open gaps and options (none done)

1. Sources for the five physical constants above.
2. The attitude blocks are passengers on a level corridor: they never change the stop point, so the 15-variable
   count overstates the relational content. Options: a downhill grade (adds g sin(grade) to the braking equation, so
   terrain and pitch carry real loss), or drop the attitude and keep the pure stop-line ladder below.
3. Decline-edge windows (see the table).
4. Whether to install the friction-rung stretch.

## Fallback: the pure stop-line ladder (not installed)

The same longitudinal refinements without attitude: L0 (p, v) -> +lag (3 states) -> +friction limit (3) -> +tyre
lag (4) -> +drag (4); losses 2.4, 1.185, 0.4, 0 m, each exact; all four CERTIFIED under every counter-run; letters
D x4. Its files were generated in the session scratchpad only; regenerate from the installed rungs by deleting the
attitude states, their ODE terms and their rows (and s, so the loss rows read p as position).

## Simulation script (stop positions)

    import math
    def sim(level, v0, psi0=0.35, dt=1e-4, eps=0.1, sb=100.0):
        p=sb-v0*eps*0.999; s=p; v=v0; b=c=0.0; psi=psi0; om=0.0; th=0.0; omt=0.0; z=0.15; omz=0.0
        phi=0.2; omphi=0.0; y=0.0; omy=0.0; t=0.0; mode='CRUISE'
        while True:
            if abs(t-round(t/eps)*eps)<dt/2:
                if mode=='CRUISE' and p>=sb: mode='BRAKE'
                elif mode=='BRAKE' and v<=0.35: mode='STOP'
            if mode=='STOP': return p, s
            tgt=3.0 if level<=1 else 2.7
            r=-psi if level<=2 else om-psi; a=v*r
            if level==0: dv=0.0 if mode=='CRUISE' else -3.0; db=dc=0
            elif level in (1,2): dv=0.0 if mode=='CRUISE' else -b; db=(tgt-b)/0.3 if mode=='BRAKE' else -b/0.3; dc=0
            else:
                dv=0.0 if mode=='CRUISE' else (-b if level==3 else -b-0.003*v*v-0.2)
                db=20*(c-b); dc=((2.7-c)/0.3 if mode=='BRAKE' else -c/0.3)
            ds=v*(1-0.5*psi*psi-(0.2*phi*phi if level>=2 else 0)) if level>=1 else v
            dpsi,dom=(-psi,0) if level<=2 else (om-psi,-om)
            dth=domt=dz=domz=dphi=domphi=dy=domy=0
            if level==2: dth=-th+0.5*z+0.02*b; dz=-z; dphi=-phi+0.015*a
            elif level==3: dth=omt-th; domt=-omt+0.5*z+0.02*b; dz=-z; dphi=-phi+0.015*a
            elif level==4:
                dth=omt-th; domt=-omt+0.5*z+0.02*b; dz=omz-z; domz=-omz
                ypp=y-2*omy+0.03*(a+9.81*phi); dphi=omphi-phi; domphi=-omphi+0.015*(a+ypp)
                dy=omy-y; domy=-omy+0.03*(a+9.81*phi)
            p+=v*dt; s+=ds*dt; v+=dv*dt; b+=db*dt; c+=dc*dt; psi+=dpsi*dt; om+=dom*dt; th+=dth*dt
            omt+=domt*dt; z+=dz*dt; omz+=domz*dt; phi+=dphi*dt; omphi+=domphi*dt; y+=dy*dt; omy+=domy*dt; t+=dt
    for v0 in (8.0, 4.0):
        print(v0, [tuple(round(x,3) for x in sim(l, v0)) for l in range(5)])

(Levels 0 to 4 are L2, L5, L8, L11, L15.)
