import YM.Poised.Sure
/-! # real use cost factorization per ray J. Uniform rate over all apertures for identifying actual physical requests, not dependent on post-J thresholds -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}{P:Flight j k}{h:l.val=c.val*P.L.val}{T:Tube su (Flight.visit P K h)}{R:BudgetPoint}
variable {X:Support l}{Y:Support c}{b b':Cover} {u v w L N p r':ℕ} {τ σ t vo vi A C M θ:ℝ}
open Kites PhysicalNext.Repeat PhysicalNext.Repeat.Brim
variable (H:TaperHol)(J:Labels.Jet su){V:Hera.Rights su N}
-- setup underlying strip capacities. All J without radius change.
structure Harbor (X:Support l)(Y:Support c)(b b':Cover)(T:Tube su (Flight.visit P K h))(R:BudgetPoint)(σ τ A vi vo t :ℝ)(u v:ℕ):Prop where
    mount : Cruising (sliceL P h) X Y b b' u v
    rows:T.R.A0.strip σ τ
    way x i j : Width σ τ (arch P i j x)
    outgoing :0 ≤ vo
    issuing :0 < vi
    binding :vo ≤ A*vi
    threshold : 0 ≤ t
    at_cost : t ≤ 2*R.threshold
    purpose : t ≤1
    charges :∀ i,Mom.needed X i→ Lyre.width R (wrap l b) i ≤1
    rank:4 ≤ k
-- orientation extra window
abbrev pups (d v:ℕ):ℝ:= (1+(v:ℝ))^(d*d)
abbrev ratioP (d n v:ℕ):ℝ:= (pups d v)^n
variable (hA:0≤ A)(hσ:0<σ)(hτ:0 ≤ τ)
include hA hσ hτ
lemma creditL (d D':ℕ): ∃ C :ℝ, 1 ≤ C ∧ ∀ (j k :ℕ)(P:Flight j k)(K:KernelChoices)(c l:Side)(h:l.val=c.val*P.L.val)(T: Tube su (Flight.visit P K h))(R:BudgetPoint)(v u:ℕ)(X:Support l)(Y:Support c)(b b':Cover)(vi vo t:ℝ), Harbor X Y b b' T R σ τ A vi vo t u v → let V:=Venture (Pipes.purseX (wrap l b) D' vi) (fun _=>1) (B:=ZBand d) (P:=R) (o:=wrap l b);∀ i≤d, V (2*C*pups d v) (craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t) ∧V (tar σ u*(C*pups d v)) (actionT d i (X:=X) (Y:=Y) (b':=b') P h T H J vo t - craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t):=by
    choose X hX hG using fun (i:Fin (d+1))=>lode_fee H J d i (Nat.le_of_lt_succ i.isLt)
    choose Y hY hP using fun (i:Fin (d+1))=>pose_fee d i (Nat.le_of_lt_succ i.isLt)
    let g(i:Fin (d+1)) (σ:ℝ) (v:ℕ) := relicG σ (d*d) (X i) v τ+ relicS σ d (d*d) (Y i) v τ*A
    let C:=1+∑ i,(g i σ 0+g i (σ/2) 0); have hz(i:Fin (d+1)){t:ℝ}(v)(h:0<t):0 ≤g i t v:=add_nonneg (relicG_pos h (hX _) hτ) (mul_nonneg (relicS_pos h (hY i) hτ) hA)
    have h0 i :0≤g i σ 0+g i (σ/2) 0:=add_nonneg (hz i 0 hσ) (hz i 0 (half_pos hσ))
    have hg:1≤C:=le_add_of_nonneg_right (sum_nonneg fun i _=> h0 i)
    have hs(i v σ) : g i σ v=g i σ 0*pups d v:=by unfold g relicG relicS ore pups; simp only [Nat.cast_zero,add_zero,one_pow,one_mul, mul_assoc]; ring
    refine ⟨C,hg,?_⟩; intro j k P K c l h T R v u S S' b b' vi vo t gK V i hi; let q : Fin (d+1):=⟨i,Nat.lt_succ_of_le hi⟩; have hv:= gK.mount; obtain ⟨a,bh⟩:=hP q vo gK.outgoing; have hq :g q σ 0+g q (σ/2) 0≤ C:= (single_le_sum (f:=fun i=> g i σ 0+g i (σ/2) 0) (fun i _=>h0 i) (mem_univ q)).trans (le_add_of_nonneg_left zero_le_one); have hp:1≤ pups d v:=one_le_pow₀ (by simp)
    constructor
    · apply Venture.absorbedM _ _ _ (giftT (d:=d) P h T R hv H J D' (hX q) (hY q) gK.threshold gK.at_cost gK.binding gK.outgoing gK.issuing hA (hG q _ gK.threshold gK.purpose) ⟨a H.T,bh⟩ hσ hτ gK.rows (fun i j x=> gK.way x i j))
      change g q σ v≤ _; rw [hs]; refine mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (hz q 0 (half_pos hσ))).trans (hq.trans ?_)) (zero_le_one.trans hp); linarith
    apply Venture.absorbedM _ _ _ (graveT (d:=d) P h T R hv H J D' (hX q) (hY q) gK.threshold gK.at_cost gK.binding gK.outgoing gK.issuing hA (hG q _ gK.threshold gK.purpose) ⟨a H.T,bh⟩ hi gK.rank hσ hτ gK.rows (fun i j x=> gK.way x i j)); rw [← mul_add]; change tar σ u*g q _ v ≤_; rw [hs]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (hz q 0 hσ)).trans hq) (zero_le_one.trans hp)) (by unfold tar; positivity)
-- no prior ep.Time.Exist after. Two families charge. Normal error ×p times v.B input gates.
lemma sealR (d D':ℕ)(V:Hera.Rights su N)(n:ℕ)(hn:n≤d)(he:d<N): ∃ C:ℝ, 1≤C ∧ ∀ (P:Flight j k)(K:KernelChoices)(c l:Side)(h:l.val=c.val*P.L.val)(T: Tube su (Flight.visit P K h))(R:BudgetPoint)(v u:ℕ)(X:Support l)(Y:Support c)(b b':Cover)(vi vo t M:ℝ)(z:ℕ), N ≤ R.order → Fintype.card (ZBand d) < z → Harbor X Y b b' T R σ τ A vi vo t u v →∀ (F:Grid l→ Lat.Fields l 6), Flame F R X (wrap l b) vi D' z M →
    ‖rayE d n vo H b' (t • J) (kite P h T F Y)‖ ≤ C*ratioP d (N+1) v*M ∧ (∀ a:ℝ,0<a→T.R.A0=linesOf P a→ d/2≤j→(∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)→ (∀ (J:Labels.Jet su)(k:ℕ), k<n→ WardBin.leading k (Beacon.moment (d:=d) H b J F)=0)→ ‖rayE d n vo H b' (t • J) (kite P h T F Y) -(Kit.slope P.L)^n • rayE d n vo H b (t • J) F‖ ≤ C*tar σ u * ratioP d (N+1) v*M):=by
    obtain ⟨C,hC,G⟩:=creditL H J hA hσ hτ d D'
    let A:= fortuneP d n V (2*C); let B:= 1+A*((2:ℝ)*2^N*C+1)
    have ha:0≤A:= estuary V (by linarith : 1≤ 2*C) 0
    refine ⟨B, le_add_of_nonneg_right (by positivity),?_⟩; intro P K c l h T R v u X Y b b' vi vo t M z hN hZ hk F hx; let Z:=C*pups d v; have ht: 0 < tar σ u:=by unfold tar; positivity; --guard
    have hi:=hk.issuing; let X':= pups d v; let ε:=tar σ u * Z; let C₀:=2*C*pups d v; have hX:1 ≤ X':=one_le_pow₀ (by simp); have hC':1 ≤ C₀:= one_le_mul_of_one_le_of_one_le (by linarith) hX; have hZ0:1≤ Z:=one_le_mul_of_one_le_of_one_le hC hX; have hM:=hx.sight.travels
    have hp:=G _ _ P K c l h T R v u X Y b b' vi vo t hk; have he':tar σ u ≤ 2:=mul_le_of_le_one_right zero_le_two (Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) u]))
    have heX: fortuneP d n V C₀=A*X'^N:=by
       unfold C₀ A fortuneP; rw [Finset.sum_mul]; apply sum_congr rfl; intro i _; unfold meritP ult X'; rw [mul_pow (2*C)]; ring
    have hk': ε ≤ C₀:=le_trans (mul_le_mul_of_nonneg_right he' (zero_le_one.trans hZ0)) (mul_assoc ..).symm.le; have hε:0 < ε:= mul_pos ht (zero_lt_one.trans_le hZ0)
    constructor
    · apply (dankT P h T R F H J V hn hx hZ he hN hk.charges hi (fun i hv=>(hp i hv).1) (fun i hv=>(hp i hv).2) hC' hk' hε).trans (mul_le_mul_of_nonneg_right ?_ hM); unfold cholate; rw [heX]; let C':= A*X'^N; change C'*(2^N*ε)+C' ≤ _; have hq:=pow_nonneg (zero_le_one.trans hX) N; have hP:0≤C':=mul_nonneg ha hq
      apply (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk' (by positivity)) hP) (le_mul_of_one_le_right hP hX)).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (show A*(2*2^N*C+1) ≤ B from le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hX) (N+1))); unfold C' C₀; rw [pow_succ]; change A*X'^N*(2^N*(2*C*X'))+A*X'^N*X'≤ A*_ * (X'^N*X'); exact le_of_eq (by ring)
    intro a hA hT hΔ hF hh; apply (cacheT P h T R F H J V hn hx hZ he hN hk.charges hi (fun i hv=>(hp i hv).1) (fun i hv=>(hp i hv).2) hC' hk' hε hT hA hk.rank hΔ hk.mount.x_safe hk.mount.length_l hF hh).trans (mul_le_mul_of_nonneg_right ?_ hM)
    unfold cholate; rw [heX]; have hx : 0 ≤ (2:ℝ)^N*C:=by positivity; --indent
    have hs: A*(2^N*C) ≤ B:=by unfold B; nlinarith [mul_nonneg ha hx]
    apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs ht.le) (pow_nonneg (zero_le_one.trans hX) _)); rw [pow_succ]; unfold X'; exact le_of_eq (by ring)
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.sealR
