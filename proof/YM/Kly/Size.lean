import YM.Kly.Calm
import YM.Work.B10
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
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
noncomputable def bloom (H:Steady V)(X': P.algebra→⋆ₐ[ℂ]ℂ):F.Kernel := fun n x=> X'.toAlgHom.toLinearMap.compMultilinearMap (meter P H n x)
local notation "G"=> bloom P H X'
variable (y: Pack F)
include H X'
lemma bless(w:Cluster F)(h: distinct w) : pointMoment (G) w=X' (M P w h):=by
     unfold pointMoment; change X' (meter P H _ (positions w) (tokens w))=_; rw [mAt P H _ h]; apply congr_arg; change M P (realize (tokens w) (positions w)) ((realized ..).2 h)= _; congr 1; exact knit w
lemma poll (hx:x∈ conf n): bloom P H X' n x v=X' (M P (realize v x) ((realized v x).2 hx)) := (readAt (bloom P H X') v x).symm.trans (bless ..)
lemma travels (hx:x∈conf n) (s:E4): G n (points fun i=> x i+s) v= G n x v:=by
      let w:= realize v x; obtain ⟨t,d,hr⟩:= Spread.place_exists (still ((realized ..).mpr hx) (s) (v:=w)); -- arguments
      let h:= (realized v x).2 hx; rw [← readAt, show realize v (points fun i=>x i+s)=carry w s from (cart v s x).symm, bless P H X' _ (still h s),← readAt,bless P H X' _ h]; refine congr_arg _ ?_
      rw [overline P H _ h (s+t) (show Slab t₀ d (carry w (s+t)) from paths w s t ▸ hr)]; exact (overline P H _ (still h s) t hr).trans (by congr 1; rw [paths])
include hX
lemma armA : ∃ φ:V.VacuumOp →L[ℂ]ℂ, ∀ x:P.algebra,φ x.val=X' x:=by
     let B:= P.algebra.toSubalgebra.toSubmodule
     let f:StrongDual ℂ B:= {X'.toAlgHom.toLinearMap with cont:= hX}; obtain ⟨φ,hφ,-⟩:= exists_extension_norm_eq (𝕜:=ℂ) (E:=V.VacuumOp) B f; exact ⟨φ,fun t=> hφ t⟩
include E Y
lemma cross (hx:x∈conf n): ContDiffAt ℝ ∞ (fun y=> G n y v) x:=by
     obtain ⟨φ,hφ⟩:= armA P H X' hX; have ht:ContDiff ℝ ∞ (⇑φ):= ContinuousLinearMap.contDiff (E:=V.VacuumOp) (F:=ℂ) (𝕜:=ℝ) (φ.restrictScalars ℝ);
     rw [show (fun y=> G n y v)=φ ∘ (mapsL P v H) from ?_]; exact ht.contDiffAt.comp x (plated P H Y E x v hx)
     ext1 y; exact (hφ _).symm
lemma elements (b:Fin n × Axis)(hx:x∈ conf n): YM.Analysis.D (Points.direction b.1 b.2) (fun y=> G n y v) x= G n x (nextLabels F v b):=by
     obtain ⟨φ,hφ⟩:= armA P H X' hX; obtain ⟨s,r,ht⟩:= Spread.place_exists ((realized v x).2 hx); rw [cart] at ht; have hr:= (in_region ..).1 ht; let T:= Points.across (n:=n) s; let f: V.H.Op →L[ℂ]ℂ:= φ.comp Cpr; let L:= f.restrictScalars ℝ; have hv:HasFDerivAt T (ContinuousLinearMap.id ℝ _) x:= (hasFDerivAt_id x).add_const (points fun _:Fin n=>s);
     have hS(w:Fin n→ F.W)(y: Points n)(hx:y∈ conf n)(hp:T y∈ region t₀ r _): G n y w=f (mac P w s r y):=by change X' _= φ (Cpr _); rw [← hφ,activeM P H y w s r hx hp]
     have h:HasFDerivAt (fun y=> G n y v) (L.comp ((columnD P r v (T x)).comp (ContinuousLinearMap.id ℝ _))) x:=by
          refine (ContinuousLinearMap.hasFDerivAt L|>.comp x ((deriv_place P Y E r v hr).comp x hv)).congr_of_eventuallyEq ?_; filter_upwards [(conf_open _).eventually_mem hx,hv.continuousAt.tendsto.eventually ((region_open ..).eventually_mem hr)] with y hy he; exact hS v y hy he
     rw [hS _ x hx hr,D,h.fderiv]; simp only[ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,columnD_column]; rfl
lemma pastures :∃ (k:ℕ)(B:ℝ), 0≤B∧∀ r:ℝ,0<r→ r ≤1 →∀ x:Points n,spaced r x→ ‖G n x v‖≤ B*r⁻¹^k:=by
     obtain ⟨k,C,hC,hK⟩:= bound_p P Y E v; obtain ⟨φ,hφ⟩:=armA P H X' hX; let f: V.H.Op→L[ℂ]ℂ:=φ.comp Cpr; refine ⟨k,‖f‖*C, mul_nonneg (norm_nonneg _) hC,?_⟩; intro r hr ht x hx; let z:=fun i: Fin n => x i timeAxis; have he :x∈ conf n:= spaced_conf hr hx
     obtain ⟨s,hs⟩:∃ s:ℝ,∀ i:Fin n,r ≤ z i + s:=by have h(i:Fin n):= eventually_ge_atTop (r-z i); obtain ⟨s,hs⟩:= (eventually_all.mpr h).exists; exact ⟨s,fun i=> (sub_le_iff_le_add'.mp (hs i))⟩ -- syntax nesting
     let t:= s • basis timeAxis; let p:= Points.across t x; obtain ⟨d,hd,h⟩ : ∃ d:ℝ,0<d ∧ ∀ i:Fin n,z i+s≤ d-r:=by
          have h (i:Fin n):= eventually_ge_atTop (z i+s+r); obtain ⟨d,hd,h⟩:= ((eventually_gt_atTop (0:ℝ)).and (eventually_all.mpr h)).exists; exact ⟨_,hd,fun i=> le_sub_iff_add_le.mpr (h i)⟩
     let D:ℝ≥0:=⟨d,hd.le⟩; have hy(i:Fin n): p i timeAxis=z i+s:=by simp [p,z,t]
     have hL: p∈ region t₀ D n:=⟨hd,Points.across_in t he,fun i=>⟨hy i|>.symm ▸ (hr.trans_le (hs i)), hy i|>.symm ▸ (lt_of_le_of_lt (h i) (show d-r<d from by linarith))⟩⟩
     have hb:buffer t₀ r D (realize v p):=by
          refine ⟨(realize_spaced ..).mpr (fun i j h=>?_),fun i hi=>?_⟩; · change r≤ dist (WithLp.ofLp (x i + t)) (WithLp.ofLp (x j+t)); simp only [WithLp.ofLp_add,dist_add_right]; exact hx _ _ h
          obtain ⟨l,hL⟩:=List.mem_ofFn.mp hi; rw[←hL]; change r ≤ p l timeAxis∧p l timeAxis≤d-r; rw[hy]; exact ⟨hs _, h _⟩
     rw[show (G n x v)= f (P.place D (realize v p)) from ?_, mul_assoc]; · exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hK _ _ _ hL hr ht hb) (norm_nonneg _))
     exact ((hφ (meter P H n x v)).symm.trans (congr_arg _ (activeM P H x v t D he hL))) -- defeq
lemma echelon (j:ℕ) : ∃ m:ℕ,∃ B:ℝ,0 ≤B ∧∀ r:ℝ,0 < r → r ≤ 1 →∀ x: Points n, spaced r x→ ‖iteratedFDeriv ℝ j (fun y=>G n y v) x‖ ≤ B*r⁻¹^m:=by
     induction j generalizing v with
     | zero=> obtain ⟨k,B,hb,ht⟩:=pastures P H Y E v X' hX; exact ⟨k,B,hb,fun r hr ht' x hx=>by rw[norm_iteratedFDeriv_zero]; exact ht r hr ht' x hx⟩ -- order
     | succ j ih=>
        choose m B hb hm using fun i:Fin n × Axis=> ih (nextLabels F v i)
        refine ⟨Finset.univ.sup m,∑ b,B b,Finset.sum_nonneg (fun b _=> hb b),fun r hr ht x hx=>?_⟩; rw [←norm_fderiv_iteratedFDeriv,Finset.sum_mul]; refine (Work.B10.norm_le_direction_sum _).trans (Finset.sum_le_sum fun i h=>?_); let f(y:Points n):= G n y v; let g(y:Points n):= G n y (nextLabels F v i); have he:= spaced_conf hr hx; let u:= Points.direction i.1 i.2; have hp:D u f=ᶠ[𝓝 x] g:= ((conf_open _).eventually_mem he).mono (fun y hy=>elements P H Y E y v X' hX i hy) -- syntax
        have h' : fderiv ℝ (iteratedFDeriv ℝ j f) x u= iteratedFDeriv ℝ j g x:=by
             ext v'; calc
                 _=iteratedFDeriv ℝ (j+1) f x (Fin.cons u v'):=by rw [iteratedFDeriv_succ_apply_left,Fin.cons_zero,Fin.tail_cons]
                 _= iteratedFDeriv ℝ j (D u f) x v':= Analysis.cons_inner ((cross P H Y E _ v X' hX he).of_le (WithTop.coe_le_coe.mpr le_top)) _ _
                 _=_:=by rw [(hp.iteratedFDeriv ℝ _).eq_of_nhds]
        change ‖fderiv ℝ _ _ u‖≤ _; rw[h']; exact (hm i r hr ht x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_inv₀ hr|>.mpr ht) (Finset.le_sup h)) (hb i))
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.echelon
#print axioms YM.Massive.Bridge.Kly.travels
#print axioms YM.Massive.Bridge.Kly.poll
#print axioms YM.Massive.Bridge.Kly.bless
