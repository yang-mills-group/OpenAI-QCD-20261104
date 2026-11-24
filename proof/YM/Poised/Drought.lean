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
include hA hp hn hu hv hN hq hf ht hκ hM U hG heV
-- tries
local notation "vZ"=> changeVars U'
lemma tape_aff : let f(s:ℝ):=framesF w (changeVars U' (f' (a.received k T q d u (increment (1:Grid c) (rod α s)) U z)))
    ContDiffAt ℝ n (shiver T F x k α qe U') 0 ∧ f =ᶠ[𝓝 0] (Xt∘ (shiver T F x k α qe U')):=by
    intro f0; let p:=display T F x k true ∘ D0; let L:=fun p:ℝ=> φ T F true (rod α p); let Q:=shiver T F x k α qe U'; let R:= D0; have h0:= announcement (F:=F) hp α N hA hN; obtain ⟨he,h⟩:= stemming (k:=k) (q:=q) (d:=d) a hp U z hu hv α
    have hh : Q=fun s=>(p s,(diffQ L U') s+U'):=by funext s; simp only [Q,p,shiver,diffQ, sub_add_cancel,L]; rfl
    refine ⟨by change ContDiffAt ℝ n Q 0; rw [hh]; exact (he.prodMk ((diff_live U' _ _ h0 hM (by omega) hκ).add contDiffAt_const)),?_⟩
    filter_upwards [h] with t ht; let g i:= su.lieExp (L t i); let W:=a.received k T q d u (increment (1:Grid c) (rod α t)) U z; have hU: f' (increment (1:Grid f) (Q t).1)= f' (Lattice.gauge g W):= heV.sites _ _ (agrees_mono ht (fun _ hx=> Finset.mem_union_left _ hx))
    change framesF w (changeVars U' (f' W))=framesF w (changeVars _ (f' (increment (1:Grid _) (Q t).1))); apply congr_arg; rw [hU,← hG g W]; exact (AlgHom.congr_fun (change_mul ..) (f' _)).symm
omit hp hq hG U heV hu hv hA hn hN hf ht hκ hM
include hq hYp hhA
lemma regular_slot (r:ℕ)(v:Fin r→ℝ)(hv:∀ i,‖v i‖≤1): Venture Y₂ w (P:=R) (o:=wrap f b) Yp (iteratedFDeriv ℝ r (s0) 0 v):=by
    have hx:0≤ Yp:=zero_le_one.trans hYp
    let L:= (route T).comp (rod α); let p:= L
    rw [show s0=(fun s=>(L s,U')) from rfl,iteratedFDeriv_prodMk (f:=L) L.contDiff.contDiffAt (g:=fun _:ℝ=>U') contDiffAt_const (le_refl _)]
    let o:=wrap f b
    refine ⟨?_,?_⟩
    · change Sized Yp (iteratedFDeriv ℝ r L 0 v) R o; have h0: Sized Yp (0:Directions su f) R o:=⟨hx,fun i=>by simp; positivity [width_pos R o i]⟩
      by_cases he:r=0; · subst r; rw [iteratedFDeriv_zero_apply,map_zero]; exact h0
      by_cases hy:r=1
      · subst r; rw [iteratedFDeriv_one_apply,L.fderiv]; change Sized Yp (route T ((v 0) • α)) R o; rw [map_smul]; refine ⟨hx,fun i=>?_⟩; rw [Pi.smul_apply,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hv _)).trans (hhA.2 i)
      rw [sterile L 0 (by omega),_root_.zero_apply]; exact h0
    change SeatD _ _ (iteratedFDeriv ℝ r (fun _:ℝ=>U') 0 v) _; by_cases he:r=0; · subst r; rw [iteratedFDeriv_zero_apply]; exact hq
    rw [iteratedFDeriv_const_of_ne he]; exact ⟨hx,fun i=>by change (∑ j, ‖orderR _ _ (0: VectorD (Site f) B) i j‖)≤_; simp [orderR,hx]⟩
include hp hq hG U heV hu hv hA hn hN hf ht hκ hM hB hΨ hqW Vb hLi hh
local notation "Rz" => mouth (1+n+Yp) Vb n nf
local notation "KW"=> Yp+W
set_option maxHeartbeats 410000 in
lemma lifespan (hW:0<W)(j:ℕ)(hj:j<n)(v:Fin j→ℝ)(hv':∀ i,‖v i‖≤1): let X(s:ℝ):=framesF w (changeVars U' (f' (a.received k T q d u (increment (1:Grid c) (rod α s)) U z)))
     ‖iteratedFDeriv ℝ j X 0 v-iteratedFDeriv ℝ j (Xt ∘ s0) 0 v‖ ≤ patterns n * ((1+(2:ℝ)^n)*(W*KW^n*Rz*τ)):=by
    intro X'
    let p:= s'; let p0:= s0; have he := hearts (k:=k) (q:=q) (d:=d) (U:=U) a hp hn z hu hv α (fun s=>(p s).1) rfl
    have hz:p0 0=(0,U'):=by simp [p0,quakes]
    have hp₁:p 0=( (p 0).1,U'):=by
       refine Prod.ext rfl ?_;  unfold p shiver; simp only [map_zero]; change hailC (sealsZ 0) U'=U'; apply flat_ext; intro i; rw [hailF]; simp [sealsZ]; exact step_one _ -- names
    let y:=p 0-p0 0
    have hx(s:ℝ):p0 0+s • y=(s • (p 0).1,U'):=by unfold y; nth_rw 1 [hz]; conv_lhs=> rw [hp₁,hz]; simp
    have hQ : 1 ≤ KW:= hYp.trans (le_add_of_nonneg_right hW.le); have hZ:= hp.rehearsed.orders; have hh0(i:ℕ)(hi:i ≤ n)(t:Fin i→ℝ)(hV:∀ j, ‖t j‖ ≤1):= engraved (k:=k) (q:=q) (d:=d) (U:=U) a hp b hn z hu hv α N Yp hA hN _ w U' fw A₀ hq ht hf hκ hM W hW.le hqW hΨ i hi t hV
    have hh₃: 0 ≤ Rz:=by unfold Pipes.mouth; have hV:=Vb.large; positivity
    have ht:= hh.1; have hΨ:Healthy R.threshold X (increment 1 (p0 0).1):=by rw [hz]; change Healthy _ _ (increment _ 0); rw [Work.G07.at_zero_increment]; exact one_healthy _ _ (R.threshold_pos.le)
    have hS': ContDiffAt ℝ n Xt (p0 0):= sighted _ _ _ heV hΨ hZ; have hP': ContDiffAt ℝ n p0 0:= ((route T).contDiff.contDiffAt.comp _ (rod α).contDiff.contDiffAt).prodMk contDiffAt_const
    have hΦ:= tape_aff (k:=k) (q:=q) (d:=d) a hp b hn U z hu hv α N Yp hA hN _ w U' fw A₀ hq (by assumption) hf hκ hM f' hG heV; have hh':Healthy R.threshold X (increment 1 (p 0).1):=by simpa only [one_smul] using he.2 1 (by simp)
    have h:j≤ n:=hj.le; have hy0:(↑j:WithTop ℕ∞)≤ ↑n:= Nat.cast_le.mpr h
    rw [hΦ.2.iteratedFDeriv (𝕜:=ℝ) j |>.eq_of_nhds]; change ‖iteratedFDeriv ℝ j (Xt ∘ p) 0 v-iteratedFDeriv ℝ j (Xt ∘ p0) 0 v‖≤ _; rw [iteratedFDeriv_comp (sighted _ _ f' heV hh' hZ) hΦ.1 hy0,iteratedFDeriv_comp hS' hP' hy0]; simp only [FormalMultilinearSeries.taylorComp, sum_apply,← Finset.sum_sub_distrib]
    let K:=(1+(2:ℝ)^n)*(W*(KW)^n*Rz*τ); have hK:0≤K:=by unfold K; positivity
    refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>K) (fun q _=>?_)).trans ((le_of_eq ?_).trans (mul_le_mul_of_nonneg_right (card_le_patterns h) hK)))
    · let T₀:= iteratedFDeriv ℝ q.length Xt; let V' (i:Fin q.length):=iteratedFDeriv ℝ (q.partSize i) p 0 (v ∘ q.emb i); let V₀' (i:Fin q.length):= iteratedFDeriv ℝ (q.partSize i) p0 0 (v ∘ q.emb i)
      have hh0' i:Venture Y₂ w (o:=wrap f b) (P:=R) W (V' i-V₀' i):= hh0 _ ((q.partSize_le i).trans h) _ (fun j=>hv' _)
      have h0' i: Venture Y₂ w (P:=R) (o:=wrap f b) Yp (V₀' i):= regular_slot b α Yp _ w U' _ hq hYp hhA _ _ (fun j=>hv' _)
      have hk(t:Fin q.length): Venture Y₂ w (P:=R) (o:=wrap f b) KW (V' t):=by
         rw [show KW=W+Yp from add_comm Yp W]; exact (sub_add_cancel (V' t) (V₀' t)) ▸ Venture.adroit _ _ _ _ _ _ (hh0' _) (h0' _)
      change ‖T₀ (p 0) V'-T₀ (p0 0) V₀'‖ ≤ K; unfold K; rw [add_mul,one_mul]; apply (norm_sub_le_norm_sub_add_norm_sub _ (T₀ (p0 0) V') _).trans; apply add_le_add
      · have hn : (p 0)=(p0 0)+y:=by unfold y; abel
        have hY:Venture Y₂ w (P:=R) (o:=wrap f b) W y:=by
            have he : Venture Y₂ w (P:=R) (o:=wrap f b) W ((iteratedFDeriv ℝ 0 p 0 0) -iteratedFDeriv ℝ 0 p0 0 0):=hh0 0 (Nat.zero_le _) 0 (by simp); simpa only [iteratedFDeriv_zero_apply] using he
        have hR : ∀ s∈Set.Icc (0:ℝ) 1, Healthy R.threshold X (increment 1 ((p0 0)+s • y).1):=fun i hi=> (hx i).symm ▸ he.2 i hi
        have h₀ (s:ℝ)(hs:s∈Set.Icc (0:ℝ) 1) (i)(hi:Mom.needed X i): ‖(p0 0+s • y).1 i‖≤1:=by rw [hx s]; change ‖s • ((p 0).1 i)‖≤_; rw [norm_smul, Real.norm_of_nonneg hs.1]; exact mul_le_one₀ hs.2 (norm_nonneg _) (he.1 i)
        -- plug hx. use by rw.
        conv_lhs=> arg 1; lhs; rw [hn]
        exact navigates f' R X b (p0 0) Y₂ w Vb Yp W hYp hW (hx:=fun i hi=>by rw [hz]; exact ⟨by simp,hLi i hi⟩) hh heV hZ (lt_of_le_of_lt q.length_le hj) hB (purse_pos _ _ _ hf) y hR h₀ (fun i hi=> (hx i).symm ▸ hq) hY hQ hk -- hx doesn't rewrite
      exact alters f' R X b (p0 0) Y₂ w Vb Yp W hYp hW hΨ (fun i hi=>by rw [hz]; exact ⟨by simp,hLi i hi⟩) hh heV hZ (lt_of_le_of_lt q.length_le hj) hB (purse_pos _ _ _ hf) hQ (fun i=> Venture.absorbedM _ _ _ (h0' i) (le_add_of_nonneg_right hW.le)) hh0' (le_add_of_nonneg_left (zero_le_one.trans hYp)) (hz.symm ▸ hq)
    · simp [K]
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.lifespan
