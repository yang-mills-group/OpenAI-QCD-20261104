import YM.QCD.Raft.Glow

/-! # independent calibration for inputs and outputs. Works any finite sigma. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Cost Push.Uniform Eyrie Stationary Quarry Run Kit Sparks Pine Revolve Orbit Birth Garden Flume YM.Next.Free Exterior
open Rudder Pearl Tavern YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n: Side}{r C Y d c a b:ℝ}{j k:ℕ}
def mingle (U:Offer 1 a c)(V:Offer 2 r d):On:= U.lamp+V.lamp
lemma crewG (P:Plan j)(hp:0<a)(he:0<r)(hC:0≤c)(hV:0≤d) :∃ u b:ℝ, 0<u ∧0 ≤b ∧∀ (U:Offer 1 a c)(V: Offer 2 r d)(v:Train j)(n:Side), Eyrie.glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (caravan P v (mingle U V) n ∘ input su n) u b:=by
  obtain ⟨u,b,hu,hb,H⟩:=lumber P
  obtain ⟨w,m,hk,hQ,J⟩:= attainable 1 hp c; obtain ⟨t,e,ht,hW,E⟩:= attainable 2 he d
  let x:= min u (min w t); have hx:0<x:= lt_min hu (lt_min hk ht); have hy:x≤min w t:=min_le_right ..
  have hm :0≤m*c:=mul_nonneg hQ hC; have hD:0≤ e*d:=mul_nonneg hW hV
  refine ⟨x,b+(m*c+e*d),hx,by positivity,fun U V v n=>?_⟩
  have hh n:=(J _ _ U.price n).reduces hx (hy.trans (min_le_left ..)) hm le_rfl; have hz n:=(E _ _ V.price n).reduces hx (hy.trans (min_le_right ..)) hD le_rfl; exact ((H n v).reduces hx (min_le_left ..) hb le_rfl).plus ((hh n).plus (hz n))
lemma boundUp (P:Plan j)(A:su.Color)(hp:0<a)(he:0<r)(hC:0≤c)(hV:0≤d): ∃ D:ℝ,∀ᶠ n: Side in atTop,∀ (U:Offer 1 a c)(V:Offer 2 r d)(v:Train j), Trims (rollG P v (mingle U V) n) D A :=by
  obtain ⟨u,b,hu,hb,H⟩:= crewG P hp he hC hV
  obtain ⟨D,hD,h⟩:= HSprice P.good; refine ⟨2*syrup u b D *‖A‖^2,h.mono fun n hn U V v=>?_⟩
  let X:= mingle U V; obtain ⟨hU,hH⟩:= car_origin P v X n (U.bright.add V.bright)
  apply rooms hu hb hD (H U V v n) _ _ A <;> rw [Function.comp_apply,input_zero,hU]
  exacts [hH,hn v]

-- coordinate projections for lowest axis
lemma familiar (a j: Axis)(i:Site n): pointT n a (i,coord j)=flashT (step 0:Site n) a (i,j):=by rw [footprint]; unfold flashT; simp [eq_comm]
lemma group_p (A:su.Color)(v: Exterior.form 1 n)(x:ℝ): input su n (x • career n 1 A v)=bird A ∘ (x • fun p:Edge (Site n)=>v (p.1,coord p.2)):=by
  funext ⟨i,j⟩; rw [encode_link]; unfold bird; congr 1; ext f; change arm _ _ _ _ _ f=_; rw [arm_apply]; simp only [Pi.smul_apply,career_apply]; change x*(A f * _)=(x*v (i,coord j))*A f;  ring
lemma chargedG (P:Plan j)(X:On)(W:Train j)(n:Side)(A:su.Color)(hx:Vital X): readP (rollG P W X n) A=priceR A (caravan P W X n):=by
  let Q:=rollG P W X n; let v:= caravan P W X n
  have h:=rigL P W X hx n
  let s:=brace (pointT n 1) A
  have h₁(x: Exterior.form 1 n)(g:Weath n)(he:∀ p:Edge (Site n),g p=x (p.1,coord p.2)):
      Jacobi.mixed (career n 1 A x) (career n 1 A x) Q 0=rectifyR A v g:=by
    let z:=career n 1 A x
    have hm:= Work.F03.line_second (show ContDiffAt ℝ 2 Q 0 from h.peak.of_le le_top) (ContinuousLinearMap.ext h.dew) z; change Jacobi.mixed z z Q 0= _
    rw [iter _ _ (show ContDiffAt ℝ ω Q 0 from h.peak), ← hm]
    let f(t:ℝ):= Real.log ‖(v (bird A ∘ (t • g))).det‖
    have ht : (fun t:ℝ=> Q (t • z))= -f:= funext fun i=> by unfold f Q rollG presG v z; rw [funext he, Function.comp_apply, group_p]; rfl
    rw [ht]; change iteratedDeriv 2 (-f) 0= -deriv (deriv f) 0; rw [iteratedDeriv_neg]; simp [iteratedDeriv_succ]
  unfold readP Raft.densityP Raft.cap Pearl.priceR; rw [site_card,Nat.cast_pow]; congr 1
  rw [show supS _ _=scoreM Q A (pointT n 1) from rfl,ratedP Q h.peak]
  exact congr_arg₂ (·+·) (h₁ _ _ (fun y=> by dsimp only [cosine,vision]; rw [familiar (n:=n) 1 y.2 y.1])) (h₁ _ _ (fun y=>by dsimp only [sineP,desire]; rw [familiar (n:=n) 1 y.2 y.1])) -- maybe x placeholder
lemma calibrated (P:Plan j)(A:su.Color)(hk:‖A‖=1)(hp:0<a)(ht:0<r)(c d:ℝ): ∃ W:ℝ,∀ᶠ n:Side in atTop,∀ (U: Offer 1 a c)(V:Offer 2 r d)(v: Train j), |readP (rollG P v (mingle U V) n) A - Pearl.chargeF *Real.log n.val|≤ W:=by
  obtain ⟨z,K,hz,hC,H⟩:= pays_all P
  let η:= min z (min a r)/4; have he : 0<η:=div_pos (lt_min hz (lt_min hp ht)) (by norm_num)
  obtain ⟨W,F⟩:= docket A hk P he K c d; refine ⟨W,F.mono fun n h U V v =>?_⟩
  obtain ⟨I,G,h,H⟩:= H v
  rename_i hn
  have hm: 4*η≤min z (min a r):= by unfold η; linarith
  have hw:= hm.trans (min_le_right ..)
  have hy : Package η K c d P v G U.W V.W:=⟨he,h.reduces (by positivity) (hm.trans (min_le_left ..)) le_rfl,H,reduction U.price (by positivity) (hw.trans (min_le_left ..)) le_rfl,reduction V.price (by positivity) (hw.trans (min_le_right ..)) le_rfl⟩
  rw [chargedG P (mingle U V) v n A (U.bright.add V.bright),show caravan P v (mingle U V) n=L₀ P v U.W V.W n from funext fun i=> add_assoc ..|>.symm, pricing A hy]; exact hn _ _ _ v G U.W V.W hy
end YM.QCD.Raft
