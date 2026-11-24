import YM.Poised.Rash
import YM.QCD.Finch.Flux
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Filter Function Set Lattice Laurent Bloch Exterior RG Precision Next.Free Next.Free.Flight Place
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}
open QCD QCD.Lat QCD.Flume QCD.Kit
private lemma fromBudget {ι : Type*} {w : ι → ℝ} {f : ι → Momentum → ℂ}(h : Moderate w f) (i:ι) : ContDiffAt ℂ ω (f i) 0:=by
   obtain ⟨σ,C,hσ,hC,h⟩:=h; apply (PolyDisc.formOf ?_).contDiffAt; filter_upwards [(cube_open σ).mem_nhds (cube_zero σ hσ)] with p hp; exact (h i).hol p hp
variable (P : Flight j t)(ht:4≤t)
abbrev lot (L:Side):ℂ:=((QCD.Kit.slope L):ℂ)*((L.val:ℂ)⁻¹)
abbrev guy (x : Cover) (a b : Lat.Fiber):Cover→ℂ:=fonts P [] (wrap P.L x) a b
include ht
lemma livesE(p:Momentum)(hp:p∈baseCube)(a b:Lat.Fiber)(x:Cover) : mode p (cellar P.L x) * Laurent.read (guy P x a b) p=∑ l:Site P.L,mode (aliasAt p l) x*(lot P.L*shout false P p l a b):=by
   rw [guy, per_f P P.legal ht [] (by simp) p hp]; unfold spread; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,listChip,List.map_nil,List.prod_nil,mul_one,Next.Free.toll,pow_one,Finset.mul_sum]; refine Finset.sum_congr rfl fun l _=>?_
   rw [← show mode p (cellar P.L x)*mode (aliasAt p l) (lift (wrap P.L x))=mode (aliasAt p l) x from ?_]; unfold lot; ring
   conv_rhs=>rw [balance P.L x]
   rw [mode_shift,← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one,mul_comm]
lemma survives_sym (a b: Lat.Fiber)(x:Cover) : ∑' z:Cover,guy P x a b z= if a=b then lot P.L else 0:=by
   have h:= livesE P ht 0 (show (0:Momentum) ∈baseCube from ⟨star_zero _,fun i=> by simp [Real.pi_pos.le]⟩) a b x; unfold Laurent.read at h; simp_rw [mode_constant,one_smul,QCD.Finch.priceH P] at h; rw [one_mul,Finset.sum_eq_single (0:Site P.L)] at h
   · rw [h,show aliasAt (0:Momentum) (0:Site P.L)=0 from toe_zero P]; by_cases hv:a=b <;> simp [hv,mode_constant,Matrix.one_apply]
   · intro i _ hi; rw [if_neg hi]; simp
   simp
omit ht in
private lemma varid (z g:ℝ→ℂ)(hz:ContDiffAt ℝ ω z 0)(hg: ContDiffAt ℝ ω g 0)(hc:z 0=0) (n k:ℕ)(hn:k<n): iteratedDeriv k (fun t=>z t^n*g t) 0=0:=by
   induction n generalizing k with
   | zero=> omega
   | succ n ih=>
      let v t:=z t^n*g t; have hv : ContDiffAt ℝ ω v 0:= (hz.pow _).mul hg
      rw [show (fun t=> z t^(n+1)*g t)=fun t=>v t*z t from funext fun t=>by unfold v; ring, iteratedDeriv_fun_mul (hv.of_le le_top) (hz.of_le le_top)]; apply Finset.sum_eq_zero; intro i hi
      have he : i≤ k:=by simpa using hi; --indent
      by_cases h:i=k
      · subst i; simp [hc]
      simp [show iteratedDeriv i v 0=0 from ih _ (by omega)]
lemma shout_alive (l:Site P.L) (a b: Lat.Fiber): ContDiffAt ℂ ω (fun p=> shout false P p l a b) 0:= fromBudget ((shout_bill P.legal ht false (fun _:Unit=>P) fun _=>l).tap a b) ()
lemma staff_v (l:Site P.L)(hl:l≠0)(a b:Lat.Fiber){Z:ℝ→Momentum}(hv:Z 0=0)(hZ:ContDiffAt ℝ ω Z 0)(f:ℝ→ℂ)(hf: ContDiffAt ℝ ω f 0)(n:ℕ)(hn:n<j):
    iteratedDeriv n (fun t=>f t*shout false P (Z t) l a b) 0=0:=by
   let v p:= area P.L (aliasAt p l); have hg:(v 0)^j=0:= P.vanishing_box hl
   let u p := view false (day P l p)*host false P p
   have hA: ContDiffAt ℂ ω v 0:=by
      have he: Differentiable ℂ v:=(Train.area_diff _).comp (by unfold aliasAt; fun_prop)
      exact (PolyDisc.formOf (Eventually.of_forall fun p:Momentum=> he p)).contDiffAt
   have hU : ContDiffAt ℂ ω (fun p=>u p a b) 0:= fromBudget ((((coil (counter P.legal (fun _:Unit=>P) (fun _=>l) (fun _=>hl)) false).times (bill_host ht false (fun _:Unit=>P))).tap a b)) ()
   have he : (fun t=> f t * shout false P (Z t) l a b)=(fun t=> v (Z t)^j*(f t*u (Z t) a b)):=by
      unfold shout; funext t; rw [if_neg hl]; change _ * (v _^j*(u (Z t) a b))=_; ring
   rw [he]; apply varid (fun t=>v (Z t)) (fun t=>f t*u (Z t) a b) _ _ (show v (Z 0)=0 by rw [hv]; exact eq_zero_of_pow_eq_zero hg) _ n hn
   · exact (show ContDiffAt ℝ ω v (Z 0) from hv.symm ▸ hA.analyticAt.restrictScalars.contDiffAt).comp (0:ℝ) hZ
   apply hf.mul; exact (show ContDiffAt ℝ ω (fun p=>u p a b) (Z 0) from hv.symm ▸ hU.analyticAt.restrictScalars.contDiffAt).comp (0:ℝ) hZ
lemma resonatesP (x : Cover) (a b : Lat.Fiber) (w : RouteProbe) (s : E4) (n : ℕ) (h : n<j) :
    let v := (P.L.val:ℝ)⁻¹
    iteratedDeriv n (ruckAt w (s+Place.seat (cellar P.L x)) (guy P x a b)) 0=
      iteratedDeriv n (fun t => tune (w (s+v • Place.seat x)) t * lot P.L * shout false P (ray w t) 0 a b) 0 := by
  classical
  intro v
  let A := guy P x a b
  let B (l : Site P.L) (t : ℝ) := tune (w s) t * mode (aliasAt (ray w t) l) x * lot P.L
  let D (l : Site P.L) (t : ℝ) := B l t * shout false P (ray w t) l a b
  have HE : ruckAt w (s+Place.seat (cellar P.L x)) A =ᶠ[𝓝 0] (fun t => ∑ l : Site P.L, D l t) := by
    filter_upwards [ray_in w] with t ht'
    rw [ruck_lift,map_add,tune_add,← through_mode, mul_assoc,livesE P ht _ ht' a b x,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; unfold D B; ring
  have hb (l) : ContDiffAt ℝ ω (B l) 0 := by
    have hA : ContDiffAt ℂ ω (fun p => mode (aliasAt p l) x) (ray w 0) := by
      unfold mode aliasAt; fun_prop
    have hB : ContDiffAt ℝ ω (fun p => mode (aliasAt p l) x) (ray w 0) := hA.analyticAt.restrictScalars.contDiffAt
    have hz : ContDiffAt ℝ ω (tune (w s)) 0 := by
      -- can use restriction from complex formula
      let f (z : ℂ) := Complex.exp ((w s:ℂ)*z*Complex.I)
      have hc : ContDiffAt ℂ ω f (Complex.ofRealCLM 0) := by unfold f; fun_prop
      have hh := (show ContDiffAt ℝ ω f (Complex.ofRealCLM 0) from hc.analyticAt.restrictScalars.contDiffAt).comp _ (ContinuousLinearMap.contDiff Complex.ofRealCLM).contDiffAt
      rw [show tune (w s)=f ∘ Complex.ofRealCLM from funext fun z => by simp [tune,f]]; exact hh
    unfold B; exact (hz.mul (hB.comp (f:=ray w) _ (ray_smooth w).contDiffAt)).mul contDiffAt_const
  have hL (l) : ContDiffAt ℝ ω (D l) 0 := by
    let f p := shout false P p l a b
    have h : ContDiffAt ℝ ω f (ray w 0) := (ray_root w).symm ▸ (shout_alive P ht l _ _).analyticAt.restrictScalars.contDiffAt
    exact (hb l).mul (h.comp _ (ray_smooth w).contDiffAt)
  change iteratedDeriv n (ruckAt _ _ A) 0 = _
  rw [HE.iteratedDeriv_eq, iteratedDeriv_fun_sum (fun l _ => (hL l).of_le le_top),Finset.sum_eq_single (0:Site P.L)]; swap
  · intro i _ hi; exact staff_v P ht i hi a b (ray_root w) (ray_smooth w).contDiffAt _ (hb i) n h
  swap; · simp
  have he (t : ℝ) : B 0 t = tune (w (s+v • Place.seat x)) t *lot P.L := by unfold B; rw [map_add, narrow_mode,tune_add]
  simp_rw [D,he]

/-- `a`th moment exactly the principal prediction on every row, on
cover coordinate powers here. Even old `x=0,L=...`, n=0. -/
lemma psalm (x : Cover)(a b: Lat.Fiber) (w: RouteProbe)(n:ℕ)(h:n<j): let q z:= guy P z a b; let s:=(P.L.val:ℝ)⁻¹ • Place.seat x
    ∑' z, ((w (Place.seat (cellar P.L x+z)):ℂ)^n) * q x z=∑' z, (w (s+Place.seat z):ℂ)^n*q 0 z:=by
   obtain ⟨σ,C,hσ,hC,hK⟩:= reserves_font P.legal ht
   intro q s; have ht':= resonatesP P ht x a b w 0 n h; have h0 := resonatesP P ht 0 a b w s n h; simp only [zero_add] at ht'; simp only [seat_zero,zero_cellar,smul_zero,add_zero] at h0
   have hv(i:Cover):Width σ _ (q i):= hK P (wrap P.L i) [] (by simp) a b
   apply mul_left_cancel₀ (show Complex.I^n≠0 by simp); convert (ht'.trans h0.symm) using 1 <;> rw [march_points w _ n hσ (hv _)] <;> simp [q,Place.seat_add]
end YM.Planned.PrimaryIntegral295.Carrier
