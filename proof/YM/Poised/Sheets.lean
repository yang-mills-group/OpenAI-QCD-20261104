import YM.Poised.Drought
import YM.Poised.Looms
import YM.Poised.Transits
import YM.Poised.Pacific
import YM.Poised.Fountain
import YM.Poised.Street
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χ R₁ :ℝ}
open PhysicalNext.Repeat Cub
-- ,g=1 even no Short; agreement common chart at identity.
variable [DecidableEq I](α: Directions su c)
local notation "F⚬"=> (1:Frame c)
local notation "V⚬"=> (1:Grid c)
local notation "qe"=> a.extra F⚬ u z
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (N Yp:ℝ)(hA:‖α‖ ≤ N*loom P (reach x) C.C) (hN:1 ≤ N)
local notation "An"=> Heir.loom P (reach x) C.C
local notation "D0"=> fun s:ℝ=> (rod α s,a.extra (1:Frame c) u z)
local notation "v0"=> route T ∘ rod α
local notation "m0"=> u*‖tape z‖
local notation "ψ₁"=> ((E).Q)
variable (i:ℕ) (w:B→ℝ)(U':VectorD (Site f) B)(fw A₀:ℝ) (hq:SeatD (purseX (wrap f b) i fw) w U' Yp) (hYp:1 ≤Yp)
local notation "Y₂"=> purseX (wrap f b) i fw
variable (ht:∀ i,w i>0)(hf:fw>0)(hκ:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→ Through n (yaw i j) x A₀)(hM:C.M*(N*loom P (reach x) C.C) ≤1)
variable (W:ℝ) (hW:0 ≤ W) (hqW: clinicFee n E.Q*loom P (reach x) C.C ^2 * N^n + u*‖tape z‖≤ W*R.threshold) (hΨ: (1+patterns n)*(A₀*(C.M*(N*loom P (reach x) C.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W)
-- comparator.Quasi.P. `mouth` constant needs path.S seat at **Yp constant**! H 0=0? φ(y=0)=0 so y.2−...=0. use exact.
variable (f':Grid f→Lat.Fields f 6)(nf:ℕ)
set_option quotPrecheck false
local notation "s0"=> quakes T α U'
local notation "s'"=> shiver T F x k α qe U'
local notation "Xt"=> (framesF w∘lotsF f')
variable (hG : ∀ k U,slots 6 k (f' (Lattice.gauge k U))=f' U) (heV:Ease.Charm R X f') (hS:∀ V,f' V∈ Creek.region (limits X)) (hB:∀ V,f' V ∈ layer (Faces (Site f)) nf)
variable (hh:R.supBounds (wrap f b) X (framesF (purseX (wrap f b) i fw)∘f') τ)(Vb:Hera.Rights su n)
variable (hhA:Sized Yp (route T α) R (wrap f b))(hLi:∀ i,Mom.needed X i→ width R (wrap f b) i ≤1)
noncomputable def cherub (T:Tube su S)(Z:VectorD (Site f) B)(H:Grid f→Lat.Fields f 6)(U:Grid c): Alg B:= changeVars Z (H (increment (1:Grid f) (route T fun i => su.plog (su.mat (U i)))))
lemma lofts (Z:VectorD (Site f) B)(F:Grid f→Lat.Fields f 6) : cherub T Z F ∘increment 1 =ᶠ[𝓝 0] fun x=> changeVars Z (F (increment 1 (route T x))):=by
    have h(e: Bond c) : ∀ᶠ y:Directions su c in 𝓝 0, su.plog (su.mat ((increment 1 y) e))= y e:=by
        have hy:= (show Tendsto (fun U: Directions su c=> U e) (𝓝 0) (𝓝 0) from (continuous_apply e).tendsto _).eventually (su.plog_left); refine hy.mono fun x hx=>?_ ; change su.plog (su.mat (su.lieExp (x e) * 1))=_; rw [mul_one]; exact hx
    filter_upwards [eventually_all.mpr h] with y hy; unfold Function.comp cherub; rw [funext hy]
include heV
lemma nest {m:ℕ}(hl:m≤R.order): Push.Local.Chart m (cherub T U' f') (1:Grid c):=by
    apply (ContDiffAt.congr_of_eventuallyEq _ (lofts (T:=T) U' f'))
    let b:=(route T); let A:= (vat U').comp (ContinuousLinearMap.id ℝ (Lat.Fields f 6)); -- comp synt
    refine A.contDiff.contDiffAt.comp (f:=fun y=> f' (increment 1 (b y))) _ ?_
    exact (show ContDiffAt ℝ (↑m) (f'∘increment 1) _ from (show b 0=0 from map_zero _).symm ▸ ((heV.smooth _ (one_healthy _ _ R.threshold_pos.le)).of_le (Nat.cast_le.mpr hl))).comp (f:=b) _ b.contDiff.contDiffAt
-- Prefix any REAL tester. Need exchange via Hera.guise (Charm from linear usage with arbitrary finite-dimensional bound can pay depends c, we use only final exchange). F input gauge not tested.
local notation "K" => cherub T U' f'
local notation "K'" => framesF w ∘ K
omit heV in
lemma genesis : (K' ∘ increment 1 ∘ rod α) =ᶠ[𝓝 0] (Xt) ∘ s0:=by
   filter_upwards [((show Tendsto (rod α) (𝓝 0) (𝓝 0) from (by simpa using (rod α).continuous.continuousAt (x:=0) |>.tendsto)).eventually (lofts (T:=T) U' f'))] with x hx using congr_arg (framesF w) hx
local notation "vz"=>changeVars U'
local notation "Vq"=>fun V:Grid c=> framesF w (vz (f' (a.received k T q d u V U z))) -- fix
omit heV in
lemma diagnosis {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](h:Grid c→E)(r:ℕ):leftDerivs h (List.replicate r α) 1 = iteratedFDeriv ℝ r (h ∘ increment 1 ∘ rod α) 0 (fun _=>1):=by
    have hm:= leftDerivs_diag (1:Grid c) α h r 0; rw [zero_smul,Work.G07.at_zero_increment] at hm; exact hm -- iteratedDeriv definitional?
include hp hq hG U hu hv hA hn hN hf ht hκ hM hB hΨ hqW Vb hLi hh hYp hhA
local notation "Rz" => Pipes.mouth (1+n+Yp) Vb n nf
local notation "KW"=> Yp+W
lemma risk (hW:0<W)(j:ℕ)(hj:j<n):
     ‖leftDerivs (Vq) (List.replicate j α) 1-leftDerivs (K') (List.replicate j α) 1‖≤ patterns n*((1+(2:ℝ)^n)*(W*KW^n*Rz*τ)):=by
   rw [diagnosis α (Vq) j,diagnosis α K' j,(genesis (T:=T) α w U' f').iteratedFDeriv (𝕜:=ℝ) j|>.eq_of_nhds]; exact lifespan a hp b hn U z hu hv α N Yp hA hN i w U' fw A₀ hq hYp ht hf hκ hM W hqW hΨ f' nf hG heV hB hh Vb hhA hLi hW j hj _ (by simp)
omit hp hn hG U hu hv hA hN ht hκ hM hΨ hqW
variable (h:n ≤ R.order)
include h
lemma costume (j:ℕ)(hj:j≤n):
    ‖leftDerivs K' (List.replicate j α) 1‖ ≤ patterns n*(Yp^n*Rz*τ):=by
    rw [diagnosis,_root_.Filter.EventuallyEq.eq_of_nhds ((genesis (T:=T) α w U' f').iteratedFDeriv (𝕜:=ℝ) j)]
    let p:= s0; have hz:p 0=(0,U'):=by simp [p,quakes]
    have ht:= hh.1
    have hΨ:Healthy R.threshold X (increment 1 (p 0).1):=by rw [hz]; change Healthy _ _ (increment _ 0); rw [Work.G07.at_zero_increment]; exact one_healthy _ _ (R.threshold_pos.le)
    have hS': ContDiffAt ℝ n Xt (p 0):= sighted _ _ _ heV hΨ h; have hP': ContDiffAt ℝ n p 0:= ((route T).contDiff.contDiffAt.comp _ (rod α).contDiff.contDiffAt).prodMk contDiffAt_const
    apply ((iteratedFDeriv ℝ j (Xt ∘ p) 0).unit_le_opNorm (show ‖(fun _:Fin j=>(1:ℝ))‖≤1 from (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp))).trans; apply slots_bound hP' hS' hj; rotate_left
    · intro Q v hv; let V:=fun i:Fin Q.length => iteratedFDeriv ℝ (Q.partSize i) p 0 (v∘ Q.emb i)
      have hQ:= Q.length_le.trans hj
      refine (risingW f' _ _ _ Vb heV hh (purse_pos _ _ _ hf) hΨ (fun i hi=>by rw [hz]; exact ⟨by simp,hLi i hi⟩) nf hB (hr:=hQ) (ht:=h) (show SeatD Y₂ w _ Yp from hz.symm ▸ hq) V (fun _=>Yp) (fun _=>zero_lt_one.trans_le hYp) (fun i'=>regular_slot b α Yp i w U' _ hq hYp hhA _ _ (fun i=>hv _))).trans ?_
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; have hh:0≤ Pipes.mouth (1+n+Yp) Vb Q.length nf:=by unfold Pipes.mouth; have ht:=Vb.large; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ hYp hQ) (bite _ _ hYp _ hQ) hh (by positivity)) ht
    unfold Pipes.mouth; have h:=Vb.large; positivity
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.risk
