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
-- local auxiliary. Clue.V.Decayment
private lemma solo (α: Directions su c) : ‖rod α‖ ≤ ‖α‖:=ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v=> by change ‖v • α‖≤ _; exact (le_of_eq (by rw [norm_smul,mul_comm]))) -- perhaps need ordering ℂ
private lemma cantL {D X:Type}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup X][NormedSpace ℝ X] (L:D→L[ℝ]X){i:ℕ} : Through i L 0 ‖L‖:=by
   refine ⟨L.contDiff.contDiffAt,fun i _=>?_⟩
   by_cases he :i=0; · subst i; rw [norm_iteratedFDeriv_zero,map_zero,norm_zero]; exact norm_nonneg _
   by_cases h:i=1; · subst i; rw [norm_iteratedFDeriv_one,L.fderiv]
   rw [sterile _ _ (by omega),norm_zero]; positivity
variable (N Yp:ℝ)(hA:‖α‖ ≤ N*loom P (reach x) C.C) (hN:1 ≤ N)
local notation "An"=> Heir.loom P (reach x) C.C
local notation "D0"=> fun s:ℝ=> (rod α s,a.extra (1:Frame c) u z)
local notation "v0"=> route T ∘ rod α
local notation "m0"=> u*‖tape z‖
local notation "ψ₁"=> ((E).Q)
variable (i:ℕ) (w:B→ℝ)(U':VectorD (Site f) B)(fw A₀:ℝ) (hq:SeatD (purseX (wrap f b) i fw) w U' Yp) (hYp:1 ≤Yp)
local notation "Y₂"=> purseX (wrap f b) i fw
variable (ht:∀ i,w i>0)(hf:fw>0)(hκ:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→ Through n (yaw i j) x A₀)(hM:C.M*(N*loom P (reach x) C.C) ≤1)
include hp hA hN
lemma announcement : Through n (fun p:ℝ=> φ T F true (rod α p)) 0 (C.M*(N*loom P (reach x) C.C)):=by
    let L:=φ T F true; have hQ:‖L‖ ≤C.M:= by unfold L Heir.φ; rw [if_pos rfl]; exact (hp.stages F).norm_phi
    apply linear_through L ((cantL (rod α)).mono ((solo α).trans hA)) hQ
omit hA hp hN
abbrev shiver (T :Tube su S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(v:Directions su c)(w:Directions su f)(Z:VectorD (Site f) B) (s:ℝ): Pipes.Path f B:= (Heir.display T F x k true (rod v s,w),hailC (sealsZ (φ T F true (rod v s))) Z)
abbrev quakes (T :Tube su S)(v:Directions su c)(Z:VectorD (Site f) B) (s:ℝ) : Pipes.Path f B := (route T (rod v s),Z)
-- bound.MCost ψ chosen later
variable (W:ℝ) (hW:0 ≤ W) (hqW: clinicFee n E.Q*loom P (reach x) C.C ^2 * N^n + u*‖tape z‖≤ W*R.threshold) (hΨ: (1+patterns n)*(A₀*(C.M*(N*loom P (reach x) C.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W)
include hp hA hN hu hv hn hW hqW
private lemma dearly (j:ℕ) (hj:j≤n)(V:Fin j→ℝ)(hw:∀ i,‖V i‖≤1):
 Sized W (iteratedFDeriv ℝ j (display T F x k true ∘ D0) 0 V - iteratedFDeriv ℝ j (route T ∘ rod α) 0 V) R o:=by
    let Y:= (rod α); let U:= D0; have he:=hp.acts F k; let uNew:= An; let p:=display T F x k true; let M:= mainStroke T F true; let g':= iteratedFDeriv ℝ j (route T ∘ Y) 0 V
    have h:=hp.rehearsed; have hrs:=h.tensions; have hw':=a.extra_size F⚬ _ hu z; have hZ:= hw'.trans (hv.trans hrs.noise); have hA':ContDiffAt ℝ n U 0:= Y.contDiff.contDiffAt.prodMk contDiffAt_const; have hS:‖U 0‖ ≤ An:=by unfold U; rw [map_zero]; exact max_le ((norm_zero).le.trans ((norm_nonneg _).trans hZ)) hZ
    let i₁:=iteratedFDeriv ℝ j U 0 V
    have hr : ‖iteratedFDeriv ℝ j (p ∘ U) 0 V - M i₁‖ ≤ clinicFee n E.Q * An^2 * N^j:= by
        have hg:= hS; have hb : 0≤ uNew:= (norm_nonneg _).trans hZ
        apply (he.costs true).propagate hn hS (zero_le_one.trans E.majorant) ?_ ?_ hrs.allows.le hA' (zero_le_one.trans hN) _ hj _ hw
        · rw [← h.temp_eq]; unfold loom; exact (le_mul_of_one_le_left P.threshold_pos.le C.C_one).trans (le_mul_of_one_le_right (by positivity [P.threshold_pos,C.C_one]) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
        · exact (le_mul_of_one_le_left hb E.majorant).trans (hrs.small.trans (min_le_right ..))
        intro j hj hl v hv; rw [iteratedFDeriv_prodMk (g:=fun _:ℝ => _) (f:=rod α) (rod α).contDiff.contDiffAt (𝕜:=ℝ) (n:=(n:WithTop ℕ∞)) contDiffAt_const (Nat.cast_le.mpr hl),iteratedFDeriv_const_of_ne (by omega)]; change max ‖iteratedFDeriv ℝ j (rod α) 0 v‖ ‖(0:Directions su f)‖ ≤ _; rw [norm_zero]; apply max_le; swap; · positivity [P.threshold_pos,C.C_one]
        by_cases he:j=1; · subst j; apply ((iteratedFDeriv ℝ 1 (rod α) 0).unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hv)).trans; simpa [mul_comm N] using (((cantL (i:=1) (rod α)).pay _ le_rfl).trans ((solo α).trans hA))
        rw [sterile (rod α) 0 (by omega),_root_.zero_apply,norm_zero]; positivity [P.threshold_pos,C.C_one]
    have hM: ‖M i₁-g'‖ ≤ m0:=by
       by_cases he:j=0; · subst j; unfold i₁ g'; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]; change ‖(route T (rod α 0)+qe)-route T (rod α 0)‖ ≤ _; rw [add_sub_cancel_left]; exact hw'
       unfold i₁ g'; rw [iteratedFDeriv_prodMk (f:=rod α) (g:=fun _:ℝ => _) (rod α).contDiff.contDiffAt (𝕜:=ℝ) (n:=(n:WithTop ℕ∞)) contDiffAt_const (Nat.cast_le.mpr hj),iteratedFDeriv_const_of_ne he,(route T).iteratedFDeriv_comp_left Y.contDiff.contDiffAt (Nat.cast_le.mpr hj)]
       change ‖(route T (iteratedFDeriv ℝ j (rod α) 0 V)+0)-route T (iteratedFDeriv ℝ j (rod α) 0 V)‖≤ _; rw [add_zero,sub_self,norm_zero]; exact (norm_nonneg _).trans hw'
    refine ⟨hW,fun i=>?_⟩; apply (norm_le_pi_norm ..).trans
    have h0: 1≤E.Q:= E.majorant
    have hξ: 0≤ clinicFee n E.Q:= le_trans (mul_nonneg zero_le_two (zero_le_one.trans E.majorant)) (clinicFee_le n (zero_le_one.trans E.majorant)) -- ar
    refine (norm_sub_le_norm_sub_add_norm_sub _ (M i₁) _).trans ((add_le_add (hr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hj) (by positivity))) hM).trans (hqW.trans ?_))
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right R.threshold_pos.le (one_le_pow₀ (by simp))) hW
include hM U hq ht hf hκ hΨ q d
lemma engraved (j:ℕ) (hj:j≤n)(V:Fin j→ℝ)(hw:∀ i,‖V i‖≤1):
 Venture Y₂ w (o:=wrap f b) (P:=R) W (iteratedFDeriv ℝ j (shiver T F x k α qe U') 0 V - iteratedFDeriv ℝ j (quakes T α U') 0 V):=by
    let Y:= U'; let L:= route T ∘ rod α; let L' := Heir.display T F x k true ∘ D0; let N':=fun p:ℝ=> φ T F true (rod α p); let H:= diffQ N' Y; let V':=H + fun _ :ℝ=>Y; have h0:= announcement (F:=F) hp α N hA hN; have he :ContDiffAt ℝ n L' 0 := (stemming (k:=k) (U:=U) (q:=q) (d:=d) a hp z hu hv α).1; have hL: ContDiffAt ℝ n L 0:= (route T).contDiff.contDiffAt.comp (f:=rod α) _ (rod α).contDiff.contDiffAt
    have hH: ContDiffAt ℝ n H 0:= diff_live Y _ _ h0 hM (by omega) hκ
    have hk:(↑j:WithTop ℕ∞) ≤ ↑n:=Nat.cast_le.mpr hj
    have hT: shiver T F x k α qe U'=fun s=>(L' s,V' s):=by funext s; unfold shiver; simp only [V',H,Pi.add_apply,diffQ,sub_add_cancel]; rfl
    rw [hT,iteratedFDeriv_prodMk (g:=V') he (hH.add contDiffAt_const) hk]
    rw [show quakes T α U'=(fun s=>(L s,(fun _:ℝ=>Y) s)) from rfl,iteratedFDeriv_prodMk (g:=fun _:ℝ=>Y) hL contDiffAt_const hk]
    refine ⟨dearly (k:=k) a hp hn z hu hv α N hA hN W hW hqW j hj V hw,?_⟩ -- order binder
    change SeatD _ _ (iteratedFDeriv ℝ j V' 0 V-iteratedFDeriv ℝ j (fun _:ℝ=> Y) 0 V) W; rw [iteratedFDeriv_add_apply (hH.of_le hk) contDiffAt_const]; change SeatD _ _ ((iteratedFDeriv ℝ j H 0 V + iteratedFDeriv ℝ j (fun _:ℝ=>Y) 0 V) - _) W; rw [add_sub_cancel_right]
    exact SeatD.less _ _ _ _ _ (line_cost Y _ _ h0 hM (by omega) hκ i (wrap f b) w hf ht hq j hj V hw) hΨ
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.engraved
