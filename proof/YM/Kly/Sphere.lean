import YM.Kly.Tele
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
lemma aspens (i:Fin n):∃ (l r:Cluster F),∀ z,realize (update v i z) x= l++(x i,z)::r:=by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih=>
       refine Fin.cases ?_ (fun i=>?_) i
       · refine ⟨[],realize (Fin.tail v) (Points.tail x),fun z=>?_⟩; unfold realize; simp only[List.ofFn_succ]; rw [update_self]; apply congr_arg (List.cons _); apply congr_arg List.ofFn; funext j; rw [update_of_ne]; · rfl
         simp
       obtain ⟨l,r,h⟩:=ih (Points.tail x) (Fin.tail v) i; refine ⟨(x 0,v 0)::l,r,fun z=>?_⟩; rw [show realize (update v i.succ z) x=(x 0,v 0)::realize (update (Fin.tail v) i z) (Points.tail x) from ?_,h]; · rfl
       unfold realize; rw [List.ofFn_succ]; apply congr_arg₂ List.cons; · rw [update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
       apply congr_arg List.ofFn; funext j; by_cases h:j=i; · rw [h]; simp[Points.tail]
       rw [update_of_ne (fun k=> h (Fin.succ_inj.mp k)), update_of_ne h]; rfl
include H
lemma lunar (hx:x∈conf n)(i:Fin n) : ∃ L:F.W→ₗ[ℂ]P.algebra,∀ z,L z=M P _ ((realized (update v i z) x).mpr hx):=by
     obtain ⟨l,r,h⟩:= aspens x v i; have he: distinct (l++(x i,v i)::r):= h (v i) ▸ (realized ..).mpr hx; obtain ⟨L,ht⟩:= inL P H _ _ _ _ he; exact ⟨L,fun z=> (ht _).trans (by congr 1; exact (h _).symm)⟩
noncomputable def lineP (H:Steady V)(x: Points n)(hx:x∈conf n):MultilinearMap ℂ (fun _ : Fin n=> F.W) P.algebra := by
     refine MultilinearMap.mk' (fun v=>M P (realize v x) ((realized ..).mpr hx)) ?_ ?_
     · intro v i b c; obtain ⟨L,h⟩:=lunar P H x v hx i; exact (h (b+c)).symm.trans ((map_add L b c).trans (congr_arg₂ (fun u v:P.algebra=>u+v) (h b) (h c)))
     intro v i b c; obtain ⟨L,h⟩:=lunar P H x v hx i; exact (h (b • c)).symm.trans ((map_smul L b c).trans (congr_arg (fun x:P.algebra=>b • x) (h c)))
noncomputable abbrev meter (H:Steady V)(n:ℕ)(x:Points n):MultilinearMap ℂ (fun _ : Fin n=> F.W) P.algebra:=by
     classical exact if h:x∈conf n then lineP P H x h else 0
lemma mAt {n:ℕ}(x:Points n)(hx:x∈conf n) : meter P H n x=lineP P H x hx:=by classical unfold meter; rw [dif_pos hx]
noncomputable def Cpr: V.H.Op →L[ℂ] V.VacuumOp := ((ContinuousLinearMap.compL ℂ V.D V.H V.D) V.D.orthogonalProjectionOnto).comp ((ContinuousLinearMap.compL ℂ V.D V.H V.H).flip V.D.subtypeL)
omit H
lemma printA (u:Cluster F)(r:ℝ≥0)(h:Slab t₀ r u): (P.slot u r h).val= Cpr (V:=V) (P.place r u):=rfl
noncomputable def mac (s:E4)(r:ℝ≥0)(x:Points n):=P.place r (realize v (Points.across s x))
variable (s:E4)(r:ℝ≥0)
lemma cart (x:Points n): carry (realize v x) s= realize v (Points.across s x):=by unfold carry realize; rw[List.map_ofFn]; rfl
include H
lemma activeM (hx:x∈conf n)(ht: Points.across s x∈ region t₀ r n) : (meter P H _ x v).val= Cpr (V:=V) (mac P v s r x):=by
     rw[mAt P H _ hx]; have hp:Slab t₀ r (carry (realize v x) s):= cart v s x ▸ (in_region ..).mpr ht; change (M P (realize v x) ((realized ..).mpr hx)).val=_; rw [overline P H _ _ s hp,printA,cart]; rfl
omit H
lemma acc (x:Points n)(s:E4) : ContDiff ℝ ∞ (Points.across (n:=n) s):= contDiff_id.add (contDiff_const (c:=points fun _ : Fin n=>s)) -- x unused
include H E Y
noncomputable def mapsL (H: Steady V) (x:Points n):V.VacuumOp:=(meter P H n x v).val
lemma plated (hx:x∈conf n):ContDiffAt ℝ ∞ (mapsL P v H) x :=by
    obtain ⟨s,r,ht⟩:=Spread.place_exists ((realized v x).2 hx); rw [cart] at ht; have hr:= (in_region ..).1 ht; let T:= Points.across (n:=n) s; let f:=Cpr (V:=V); have hm:ContDiffAt ℝ ∞ (mac P v s r) x:= (((smooth_place P Y E r v).contDiffAt ((region_open ..).mem_nhds hr)).comp x (acc x s).contDiffAt)
    have hΔ: ContDiff ℝ ∞ (fun z:V.H.Op=>Cpr (V:=V) z):= ContinuousLinearMap.contDiff (E:=V.H.Op) (F:=V.VacuumOp) (𝕜:=ℝ) ((Cpr (V:=V)).restrictScalars ℝ);
    have hT:ContDiffAt ℝ ∞ (fun y=>f (mac P v s r y)) x:= hΔ.contDiffAt.comp x hm
    refine hT.congr_of_eventuallyEq ?_; filter_upwards [(conf_open _).eventually_mem hx,(acc x s).continuous.continuousAt.eventually ((region_open ..).eventually_mem hr)] with y hy hp; exact activeM P H y v s r hy hp
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.plated
#print axioms YM.Massive.Bridge.Kly.lineP
