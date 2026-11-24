import YM.QCD.Dust.June
/-! # Warp inventory BEFORE step. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform Patron Reggae AnalyticBridge.LocalGaussian.Moments AnalyticBridge.VerifiedReset
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
-- Merchant Pose warp input real.F; waves future height purchase metadata separate.
open scoped Topology ContDiff Matrix.Norms.L2Operator BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
lemma mints (C:ℝ)(hc:0<C): ∃ N:ℕ,∀ L:Side,N≤ L.val→640*C*cape L 0≤1:=by
    obtain ⟨n,hn⟩:= exists_nat_ge (640*C); refine ⟨n,fun L hL=>?_⟩
    let l:ℝ:=L.val; let b:=Kit.slope L; have ht:1≤l:= Nat.one_le_cast.mpr L.property; have hp:0 < l:=zero_lt_one.trans_le ht; have hb:b ≤ 1:= by unfold b Kit.slope; apply inv_le_one_of_one_le₀; nlinarith only [Real.sqrt_nonneg l, Real.sq_sqrt hp.le, ht]
    change 640*C* (b*l⁻¹^_ )≤_; rw [show (l⁻¹)^ (1+0)=l⁻¹ by simp,← mul_assoc]; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hb) (inv_nonneg.mpr hp.le)) ((mul_le_mul_of_nonneg_right (hn.trans (Nat.cast_le.mpr hL)) (inv_nonneg.mpr hp.le)).trans_eq (mul_inv_cancel₀ hp.ne'))
def enlargement (N:ℕ):ℝ:=fareG 2 1 N
lemma blooms (hj:4≤j)(hk:4 ≤ n)(Y:ℝ)(hv:1≤Y)(N:ℕ) : ∃ C:ℝ,0<C ∧ ∃ M:ℕ,∀ L: Side, M ≤ L.val → ∀ (P:Flight j n),P.L=L→∀ (c f:Side)(e:f.val=c.val*P.L.val) (o:Site f)(W w:ℝ),0<W→0<w→w≤Y*W→ Warp L o ((sliceL P e).parent o) (ply P e) N W w ((enlargement N)⁻¹ * W) C:=by
    let z:= stemF N; let q:= enlargement N; have hz:0≤z:=by unfold z stemF Jets.Sun.fingers; positivity
    have hq:1≤q :=by unfold q enlargement fareG; change 1≤2*(2*(1+z))*1; linarith; -- indent
    obtain ⟨K,hk',H⟩:= caper hj hk 2; let X:= 1+z*K*Y*q; have hX:0<X:=by unfold X; positivity
    obtain ⟨t,ht⟩:= mints X hX
    refine ⟨X,hX,t,fun L hL P hP c f e o W w hW hw hr=>?_⟩
    subst L
    let g := q⁻¹ *W; have hg:0<g:=by unfold g; positivity
    have hc := H P c f e; let i:= cape P.L 0; have hi:0 < i := cape_pos ..
    have hA: z * K*i*w ≤ X*g*i:= (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ z*K*i)).trans (show z*K*i*(Y*W) ≤ X*g*i by
       let p:= z*K*Y*q
       have hp:p≤X:=le_add_of_nonneg_left zero_le_one
       refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hg.le) hi.le); unfold p g; field_simp)
    have he(u:ℝ)(hu:0<u)(hh:g ≤u)(z:Accent N): Lien (Stew.lens ((sliceL P e).parent o)) (fern P.L) w (X*u*i) (staff o (ply P e) z):= fareP P e K hw (fun x u h=> hc u h x) _ (by positivity) (hA.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hX.le) hi.le)) o z
    have h1 : fareG 2 g N=q*g:=by unfold fareG q enlargement; rw [fareG]; ring
    refine ⟨he W hW ?_,?_, ht P.L hL,hX.le,hw,hW,hg,?lo⟩; rotate_left -- edit
    · intro v; have h:= taxi (L':=P.L) (fun z=> he g hg le_rfl z) hw hg hX.le (ht P.L hL) v (L0Proof v); rwa [pow_zero,one_mul] at h
    case lo => change fareG 2 g N ≤ _; rw [h1,show q*g=W by unfold g; field_simp]
    exact mul_le_of_le_one_left hW.le (inv_le_one_of_one_le₀ hq)
where L0Proof {A:Type}[Fintype A](x:Alg A)(i:Finset A)(h:i.card < 0): coef i x=0:=by omega
-- calendar smallness from BK. hP Sense.
open ConnectedActivityE6
lemma prices (C:Libretto su n)(Z:Hera.Rights su n)(L:Side)(m:ℕ): ∀ᶠ u in atTop,∀ P:BudgetPoint,P.threshold≤2*fiery su u L→P.power=m → C.M*loom P (reach u) C.C ≤1 ∧ tender Z 1 (C.M*loom P (reach u) C.C) ≤ fern L^5:=by
    let v(i:ℝ):=C.M*(C.C*(2*fiery su i L)*(1+(reach i:ℝ))^m)
    let f (i:ℝ):=(1+(reach i:ℝ))^m; have hp:Rate su L 0 f:=by
       unfold f Heir.reach; push_cast; exact (((Rate.const 1).add (((Rate.const 45).mul (((Rate.const 1).add (Rate.radius_price (G:=su) (L:=L))))).weaken (by linarith))).pow m).weaken (by norm_num)
    have hx: Rate su L (-(1/2)) v:= ((((Rate.flame.mul_left 2).mul_left C.C).mul hp).weaken (by linarith)).mul_left C.M
    let A:= |tender Z 1 1|
    have he(p:ℝ)(he:0≤p): tender Z 1 p ≤ A*p:=by
       have hm:tender Z 1 p=tender Z 1 1 * p:=by unfold tender grain; ring
       exact hm.trans_le (mul_le_mul_of_nonneg_right (le_abs_self _) he)
    filter_upwards [hx.below (by norm_num) 1 zero_lt_one,(hx.mul_left A).below (by norm_num) _ (show 0<fern L^5 by positivity [fern_pos L])] with i hz hp P hV hk
    have hX:C.M*loom P (reach i) C.C ≤ v i:=by unfold v loom; rw [hk]; have hx:=C.matins; have hy:=C.C_one; gcongr
    exact ⟨hX.trans ((le_abs_self _).trans hz),(he _ (by unfold loom; positivity [C.matins,C.C_one,P.threshold_pos])).trans ((mul_le_mul_of_nonneg_left hX (abs_nonneg _)).trans ((le_abs_self _).trans hp))⟩
end YM.QCD.Dust
