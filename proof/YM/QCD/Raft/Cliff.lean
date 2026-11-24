import YM.QCD.Raft.Dock

/-! # accepted χ prices with harmonic orientation refund. accumulation at the identity -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α:ℝ}
variable (P:Plan j)(L:Plan k)(V:Back E K j k p u v) (R:Avenue V η Ω Θ)
variable {T:On} {U: Ornament t C}{W:Ornament t C}

def profG (P:Plan j)(V: Back E K j k p u v)(a:su.Color)(U:On)(i:ℕ):ℝ:= scoreM (purchaseG V P U i) a (pointT _ 1)/densityP (V.chain.n i)
abbrev diagK (n:Side)(H:Bed)(a:su.Color):= (let p:=arm su n 1 (poke a n).1; let q:=arm su n 1 (poke a n).2; Bid.gaugeFiscal H p p+Bid.gaugeFiscal H q q)
variable (hp: Skies P V T R.D' U.page W.page α r G)
lemma le_scent {D b C:ℝ}(hv:‖D‖≤ b*C)(hb:b≤a)(hh:0 ≤ C): ‖D‖≤a*C:=hv.trans (mul_le_mul_of_nonneg_right hb hh)
lemma zoom {s:ℕ→Side}(hs:Tendsto s atTop atTop)(h:0<r): Tendsto (fun n=> Real.exp (-r*(s n).val)/(Pearl.beamH (s n))^2) atTop (𝓝 0):=by
  have ht := (Run.tides ( (2*Real.pi)^2)⁻¹ 2 h).comp (Free.exhausting.comp hs)
  exact ht.congr' (Eventually.of_forall fun i=>by change ((2*Real.pi)^2)⁻¹*((s i).val:ℝ)^2*Real.exp _=_; unfold Pearl.beamH; dsimp only [Function.comp_apply]; field_simp)
include hp
lemma unilink {N: Ornament t b}(H:∀ i,Duet (litG V U.page i) (barG N.page (V.chain.n i))) (i):ContDiffAt ℝ ω (purchaseG V P T i) 0:=by
  have hs:ContDiffAt ℝ ω (purchaseG V P T i+ litG V U.page i-litG V U.page i) 0:= (hp i).1.sub (H i).leftF; rwa [add_sub_cancel_right] at hs
lemma ferry (x:su.Color)(hx: ‖x‖=1)(hw:0 < η)(ht:0<t)(hi:t≤η/2)(hr:0<r)(hG: 0 ≤ G): Tendsto (profG P V x T) atTop (𝓝 α) :=by
  obtain ⟨Z,hZ⟩:=inheritG V R U hw ht hi
  let S:= V.chain.n; let K:= R.D'
  let y (i:ℕ):= (α*diagK (S i) K x+scoreM (barG W.page (S i)) x (pointT _ 1)- scoreM (barG Z.page (S i)) x (pointT _ 1))/densityP (S i)
  have hS:= (smokeSig V R hw).goes
  have hy:Tendsto y atTop (𝓝 α):=by
    have hx:= (((metric_limit K x R.merits hw R.home hx).comp hS).const_mul α).add ((windPrice W ht x).comp hS) |>.sub ((windPrice Z ht x).comp hS)
    simp only [mul_one,add_zero,sub_zero] at hx; refine hx.congr' (Eventually.of_forall fun i=> ?_); dsimp only [y,diagK,S,Function.comp_apply]; ring
  have hT:Tendsto (fun i=> profG P V x T i - y i) atTop (𝓝 0):=by
    let d(i):= Real.exp (-r*(S i).val)/(Pearl.beamH (S i))^2; let A:= ‖sun 1‖
    apply squeeze_zero_norm' (a:=fun i=>2*(G*A^2)*d i) _ (by simpa only [mul_zero] using! ((zoom hS hr).const_mul (2*(G*A^2))))
    refine Eventually.of_forall (fun i=> ?_); let v (a:ℕ→ Atom su 2):= barG a (S i); let p:=poke x (S i); let U':=purchaseG V P T i; have hm: ContDiffAt ℝ ω U' 0:= unilink P V R hp hZ i
    let F:=cap (S i)*G*Real.exp (-r*(S i).val)
    have hl :F≥ 0:=by unfold F; have hv:=cap_pos (S i); positivity
    let B:= F*A^2
    have hu (z: Cnr (S i)) (hc:z=p.1∨z=p.2): ‖Jacobi.mixed z z U' 0+Jacobi.mixed z z (v Z.page) 0-(α*Bid.gaugeFiscal K (arm _ _ _ z) (arm _ _ _ z)+Jacobi.mixed z z (v W.page) 0)‖≤ B :=by
      rw [← (hZ i).rep, ← summed z z hm (hZ i).leftF]; apply ((hp i).2.2 z).trans
      have h' : (↑(S i).val:ℝ) ≤ (localG V i).val:=by exact_mod_cast (show (S i).val≤ _ from (divides0 V.fly V.chain i) ▸ (Nat.le_mul_of_pos_right _ V.fly.L.property)) -- inspect
      have hg : ‖z‖≤ A:=by obtain ⟨h,hp⟩:= size_brace (step 0:Site (S i)) (sun 1) x; rw [hx,one_mul] at h hp; rcases hc with hc|hc <;> rw [hc] <;> first| exact h| exact hp
      unfold B; change cap (S i) * (G*_)*_≤_; rw [← mul_assoc]; apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) hg 2) (sq_nonneg _) hl; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (cap_pos _).le hG); exact Real.exp_monotone (mul_le_mul_of_nonpos_left h' (neg_nonpos.mpr hr.le))
    have hs' : ‖scoreM U' x (pointT _ 1)-(α*diagK (S i) K x+scoreM (v W.page) x (pointT _ 1)-scoreM (v Z.page) x (pointT _ 1))‖ ≤ B+B := by
      let l z:= Jacobi.mixed z z U' 0+Jacobi.mixed z z (v Z.page) 0-(α*Bid.gaugeFiscal K (arm su _ 1 z) (arm su _ 1 z)+Jacobi.mixed z z (v W.page) 0)
      rw [ratedP U' hm,ratedP _ (zen (W.cost ht) ht _),ratedP _ (hZ i).rightF]; apply le_trans _ ((add_le_add (hu p.1 (Or.inl rfl)) (hu p.2 (Or.inr rfl))))
      refine le_trans (le_of_eq (show ‖(_:ℝ)-_‖=‖l p.1+l p.2‖ from ?_)) (norm_add_le (l p.1) (l p.2)); unfold l v diagK p S poke; congr 1; ring
    unfold profG y; rw [← sub_div, norm_div,Real.norm_of_nonneg (density_pos _).le]
    refine (div_le_div_of_nonneg_right hs' (density_pos _).le).trans_eq ?_; unfold B F d densityP; field_simp [(cap_pos _).ne', (Pearl.beamP _).ne']; unfold S; ring
  have hh := hT.add hy; simpa only [zero_add, Pi.add_def,sub_add_cancel] using! hh
end YM.QCD.Raft
