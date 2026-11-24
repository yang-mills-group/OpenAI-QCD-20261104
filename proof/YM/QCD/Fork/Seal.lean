import YM.QCD.Fork.Ridge
/-! # criterion on every endpoint, gauge slice inward
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fork
open Lat Kit Lattice Wilson RG Run Leaf Tee Function Finset Metric Filter
open Orbit Flume Sparks Quarry Pine QCD.Cost Eyrie Revolve Rudder
set_option quotPrecheck false
open scoped Matrix.Norms.Frobenius in
def frobP (X:su.Mat):=‖X‖
open scoped Matrix.Norms.L2Operator in
def colorLen (X:Mat):= ‖X‖
open scoped Matrix.Norms.Frobenius in
lemma frob_entry (X:su.Mat) (i j) : ‖X i j‖ ≤ frobP X := by
 rw [frobP,Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]; push_cast; rw [Real.le_sqrt (by positivity) (by positivity)]; norm_cast; exact le_trans (Finset.single_le_sum (s:=univ) (f:=fun j=>‖X i j‖^2) (fun i _=>by positivity) (mem_univ j)) (Finset.single_le_sum (s:=univ) (f:=fun i=>∑ j, ‖X i j‖^2) (fun i _=>by positivity) (mem_univ i))
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {I V: Type*}[Fintype I][Fintype V]{L f:Side}{x y : Site f}{a:Slot}{ξ t p C D':ℝ}{u:I→Site f}{v: V→Site f}{U: Support f}{B b m:ℕ}{H:Grid f→ArrayL I V}{X:Land f I V}{Y:Pays f I V}
-- from chord to Matrix norm
def colourRead (x:su.Mat) (i j:Hue):ℂ:= (show Mat from x) i j
lemma su_compare : ∃ C:ℝ,0<C∧∀ x:su.Mat,colorLen x ≤ C*frobP x:=by
  -- via sum elementary Matrix norm or finite dimension CLM between sup
  let Q : (((i j : Fin 3) → ℂ))→ₗ[ℂ] Mat:= LinearMap.id
  have hp:∀ x:su.Mat,‖(fun (i j:Hue)=>colourRead x i j)‖≤frobP x:=by
    intro x; have hh(i j):‖colourRead x i j‖≤frobP x:=frob_entry x i j; exact (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hh 0 0))).mpr fun i=> (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hh 0 0))).mpr (hh i)
  let K:=Q.toContinuousLinearMap; have he:0 ≤ ‖K‖:=norm_nonneg K
  refine ⟨1+‖K‖,by positivity,fun x=>?_⟩
  have hx := mul_le_mul (le_add_of_nonneg_left (show 0≤ (1:ℝ) by norm_num) : ‖K‖ ≤ _) (hp x) (norm_nonneg _) (by positivity); exact (K.le_opNorm _).trans hx
lemma halo_chart : ∃ c:ℝ,0<c∧∀ x:su.El, ‖colour x-1‖≤c*su.chord x :=by
  obtain ⟨C,hc,h⟩:=su_compare
  have hi:= su.colorScale_pos
  refine ⟨C * Real.sqrt su.repDim,mul_pos hc hi,fun x=>?_⟩
  have hx:‖colour x-(1:Mat)‖ ≤ C * frobP (su.mat x-1):=h (su.mat x-1)
  change _ ≤ _ * (frobP _/su.colorScale)
  convert hx using 1; field_simp; rw [mul_comm]; rfl
abbrev nearby (V: Grid f)(x: Site f) (b:ℕ)(t:ℝ):=Healthy t (Lattice.halo b {x}) V
lemma station (V: Grid f)(x:Site f) (b:ℕ) (he:nearby V x b t) (q:Site f) (h:separation x q≤ b)(a:PlaqAxes): su.chord (faceValue V (q,a))≤ t:=by
  by_contra! hp; apply Finset.disjoint_left.mp he (halo_spec.mpr ⟨_,mem_singleton_self _,h⟩) ((flags_spec ..).2 ⟨(q,a),List.mem_toFinset.mpr (List.mem_cons_self),hp⟩)

def rider (V: Grid f) (b:ℕ)(x:Site f): Grid f := fun i=> if separation x i.1≤b then V i else 1
lemma renting (U:Grid f)(x:Site f)(t:ℝ)(b:ℕ)(ht:0≤t)(h:∀ i:Edge (Site f),separation x i.1 ≤ b → ‖colour (U i)-1‖≤ t): ‖settled (rider U b x)-settled 1‖ ≤ t:=by
  let Q:= rider U b x
  have hf (i:Edge (Site f)) : ‖colour (Q i)-1‖≤t:=by unfold Q rider; split <;> first| exact h i ‹_›| (simp only [show colour 1=1 from rfl,sub_self,norm_zero]; exact ht) --simpa using ht
  refine (max_le ?_ ?_)
  · exact (pi_norm_le_iff_of_nonneg ht).2 fun i=> hf i
  apply (pi_norm_le_iff_of_nonneg ht).2
  intro i; change ‖star (colour (Q i))-star (1:Mat)‖≤ t; rw [← star_sub,norm_star]; exact hf i
lemma fit (x:Site f)(b:ℕ){W:Grid f}: Agrees (trunkFt x b) W (rider W b x):=by
  intro i hi hj; unfold rider; rw [if_pos]; obtain ⟨p,hp,h⟩:=halo_spec.mp hi; exact (mem_singleton.mp hp) ▸ h
lemma travelQ : ∃ Q:ℝ,0<Q ∧∀ (b:ℕ)(f:Side)(t:ℝ)(U:Grid f)(o:Site f), 2*(b+1)<f.val →0 ≤ t → nearby U o (b+1) t →∃ d:Frame f, ‖settled (rider (gauge d U) b o)-settled 1‖ ≤ Q*(b+1:ℝ)^5*t:=by
  obtain ⟨c,hc,h⟩:=halo_chart
  let a:ℝ:=Fintype.card PlaqAxes; have ha:0<a :=by unfold a; exact_mod_cast (@Fintype.card_pos PlaqAxes _ ⟨⟨(0,1),by decide⟩⟩)
  refine ⟨16*3^5*a*c,by positivity,fun b f t U o he hu ht=>?_⟩
  obtain ⟨z,hz⟩:= YM.Work.E08.axial_patch o U b (b+1) le_rfl he t hu (station U o (b+1) ht)
  refine ⟨z, renting (gauge z U) o _ b (by positivity) ?_⟩ -- U'
  intro i hi; apply (h _).trans; apply (mul_le_mul_of_nonneg_left (hz i hi) hc.le).trans; push_cast; unfold a; calc
    _ ≤ c*(16*(3*(b+1:ℝ))^5*a*t):=by gcongr <;> linarith
    _ = _:=by unfold a; ring

lemma TouchConserve (d k : su.El)(B: Bundle): ‖touch (colour d)*B *star (touch (colour k))‖= ‖B‖:=by
  have h (x:su.El): touch (colour x)∈unitary _:=touch_u ⟨su.mat_star_mul _,su.mat_mul_star _⟩ -- syntax
  let G:= touch (colour d); let K:=star (touch (colour k)); have hg:G∈unitary _:=h _; have hp:K∈unitary _:=Unitary.star_mem (h k)
  have he (Q Z:Bundle)(h:Q∈unitary _): ‖Q*Z‖≤ ‖Z‖∧ ‖Z*Q‖ ≤ ‖Z‖:=⟨(norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (rotation_price h)), (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (rotation_price h))⟩
  refine le_antisymm ((he K (G*B) hp).2.trans (he G B hg).1) (le_trans (le_of_eq ?_) ((he (star K) _ (Unitary.star_mem hp)).2.trans (he (star G) (G*B*K) (Unitary.star_mem hg)).1))
  rw [← mul_assoc,← mul_assoc, hg.1,one_mul,mul_assoc,hp.2,mul_one]

lemma payProbe {M:Pulse f→Bundle} {q:Site f}{F:Frame f} (hp:Crop x y ξ (trunkFt q b) M C) {W:Grid f} (hr: ‖settled (rider (gauge F W) b q) -settled 1‖ ≤D')(he:D'<ξ/2)(hg:0<ξ): ‖M (settled W)‖ ≤ ‖M (settled 1)‖+ C/(ξ/2)*D':=by
  let H:= rider (gauge F W) b q
  have hi : M (settled H)=touch (colour (F x))*M (settled W)*star (touch (colour (F y))):=(hp.2.2.2.2.1 (gauge F W) H (fit q b)).symm.trans (hp.2.2.2.2.2 W F)
  rw [← TouchConserve (F x) (F y),←hi]
  have hZ (x')(h : x'∈ball (settled (1:Grid f)) ξ): x'∈Kingdom f ξ:=Set.mem_iUnion.mpr ⟨1,h⟩
  have hf : settled H∈ball (settled (1:Grid f)) (ξ/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact hr.trans_lt he
  have hh:= lastwig M hg (fun i hi => hp.2.2.1 _ (hZ i hi)) (fun i hi => hp.2.2.2.1 _ (hZ i hi)) hf
  have ht := hp.1; linarith [(norm_sub_norm_le ..).trans (hh.trans (mul_le_mul_of_nonneg_left hr (show 0 ≤ C/(ξ/2) by positivity)))]
end YM.QCD.Fork
