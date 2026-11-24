import YM.Vern.City
/-! Polar conjugation via converging Gram: limit cannot lose weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Filter Set
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
variable (G:Tide X)(T:Tide W)(U:ℕ→Tide X) (hx:∀ x y,Tendsto (fun k=> (U k).knot x y) atTop (𝓝 (G.knot x y)))
variable (E:ℕ→ W≃ₗ[ℂ] X)(hE:∀ i x y,(U i).knot (E i x) (E i y)=T.knot x y)
include hx
lemma knot_seat(p q:X)(u v:ℕ→X)(hu:Tendsto u atTop (𝓝 p))(hv:Tendsto v atTop (𝓝 q)): Tendsto (fun i=> (U i).knot (u i) (v i)) atTop (𝓝 (G.knot p q)):=by
      apply Iceberg.follows_L (fun i=> (U i).zz (u i)) (G.zz p) _ _ q hv; intro x
      change Tendsto (fun i=> (U i).knot (u i) x) _ _; simp_rw [show ∀ i:ℕ, (U i).knot (u i) x= star ((U i).knot x (u i)) from fun i=>((U i).con ..).symm]; rw [show G.zz _ x=star (G.knot x p) from (G.con ..).symm]; exact (Tendsto.star (Iceberg.follows_L (fun i=>(U i).zz x) (G.zz x) (hx x) _ p hu))
lemma pier_pos : ∃ c:ℝ,0<c ∧ ∀ᶠ i in atTop,∀ u:X,‖u‖=1→c ≤ ((U i).knot u u).re:=by
      by_contra! hh
      have h(k:ℕ):∃ i ≥ k,∃ u:X,‖u‖=1∧ ((U i).knot u u).re < ((k:ℝ)+1)⁻¹:=by
           obtain ⟨i,hp,he⟩:=(hh _ (show 0<((k:ℝ)+1)⁻¹ by positivity)).and_eventually (eventually_ge_atTop k)|>.exists; exact ⟨i,he,hp⟩ -- ensure hh `Frequently`
      choose f hF u hu hz using h
      letI :ProperSpace X:=FiniteDimensional.proper ℂ _
      obtain ⟨y,hy,g,hg,ht⟩:= (isCompact_sphere (0:X) 1).tendsto_subseq (fun i=> Metric.mem_sphere.mpr ((dist_zero_right ..).trans (hu i)))
      have hf:Tendsto f atTop atTop:= tendsto_atTop_mono hF tendsto_id
      have he:= knot_seat G (U ∘ f ∘ g) (fun x y=>(hx x y).comp (hf.comp hg.tendsto_atTop)) y y _ _ ht ht; have hp:(G.knot y y).re ≤ 0:= le_of_tendsto_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp he) (show Tendsto (fun i=> ((g i:ℝ)+1)⁻¹) _ _ from ((show Tendsto (fun i:ℕ=> ((i:ℝ)+1)⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).comp hg.tendsto_atTop)) (fun i=> (hz (g i)).le)
      refine not_le_of_gt (G.positive y ?_) hp; rintro rfl; simpa using hy
include hE
lemma bolts(v:W):∃ c:ℝ,∀ᶠ k in atTop,‖E k v‖≤c:=by
      obtain ⟨c,hc,h⟩:= pier_pos G U hx; let m:=(T.knot v v).re
      refine ⟨Real.sqrt (m/c),?_⟩; filter_upwards [h] with k h
      let g:= E k v; by_cases he:g=0; · rw [show E k v=0 from he,norm_zero]; exact Real.sqrt_nonneg _
      have hw:0<‖g‖:=norm_pos_iff.mpr he; let f:ℝ:=‖g‖⁻¹; have hp:0<f:=inv_pos.mpr hw; specialize h ((f:ℂ) • g) (by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hp.le]; exact inv_mul_cancel₀ hw.ne')
      rw [(U k).seals,(U k).sep, Complex.star_def, Complex.conj_ofReal,Complex.re_ofReal_mul,Complex.re_ofReal_mul,show (U k).knot g g=_ from hE k v v] at h
      change ‖g‖≤ _; rw [← Real.sqrt_sq (le_of_lt hw)]; apply Real.sqrt_le_sqrt; rw[le_div_iff₀ hc]; unfold f at h; have hh:= (le_inv_mul_iff₀ hw).mp ((le_inv_mul_iff₀ hw).mp h) -- once h: c≤ n⁻¹*n⁻¹*m simplifies
      rwa [pow_two,mul_assoc]
lemma tended :∃ (f:ℕ→ℕ)(Q:W≃ₗ[ℂ]X), StrictMono f ∧ (∀ y,Tendsto (fun i=>E (f i) y) atTop (𝓝 (Q y)))∧∀ x y,G.knot (Q x) (Q y)=T.knot x y:=by
      let B:= Module.finBasis ℂ W; let D:= Module.finrank ℂ W; let I:= Fin D; let P(i:ℕ)(j:Fin D):= E i (B j)
      choose c hc using fun i:Fin D=> bolts G T U hx E hE (B i)
      let K:= Set.pi Set.univ (fun i:Fin D=>Metric.closedBall (0:X) (c i)); haveI :ProperSpace X:= FiniteDimensional.proper ℂ X; have hP: IsCompact K:=isCompact_univ_pi fun i=>isCompact_closedBall ..
      have h:∀ᶠ i in atTop,P i∈K:= (eventually_all.mpr hc).mono fun i hi j _ => Metric.mem_closedBall.mpr ((dist_zero_right ..).le.trans (hi j))
      obtain ⟨v,hV,f,hF,hY⟩:= hP.tendsto_subseq' h.frequently
      let Q:=B.constr ℂ v; have he(w:W) : Tendsto (fun i:ℕ=>E (f i) w) atTop (𝓝 (Q w)):=by
           rw[← B.sum_repr w]; simp_rw[_root_.map_sum,map_smul, show ∀i,Q (B i)=v i from fun i=> B.constr_basis _ _ _]; exact tendsto_finsetSum _ (fun i _=>tendsto_const_nhds.smul (tendsto_pi_nhds.mp hY i))
      have H(x y:W): G.knot (Q x) (Q y)=T.knot x y:= by
           have hp:= knot_seat G (U ∘ f) (fun x y=>(hx x y).comp hF.tendsto_atTop) _ _ _ _ (he x) (he y); exact tendsto_nhds_unique hp (tendsto_const_nhds.congr' (Eventually.of_forall (fun i=>(hE _ _ _).symm)))
      have H' : Injective Q:= LinearMap.ker_eq_bot.mp (bot_unique fun i hi=> by
                   change i=0; have hv:T.knot i i=0:=(by rw [←H,show Q i=0 from hi,Tide.zero']); by_contra ht; have h:= T.positive i ht; rw [hv] at h; exact lt_irrefl _ h)
      exact ⟨f,LinearEquiv.ofBijective Q ⟨H', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (E 0).finrank_eq).mp H'⟩, hF, he,H⟩
end YM.Vern
#print axioms YM.Vern.tended
