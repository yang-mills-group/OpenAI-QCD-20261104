import YM.Elms.Sizer
/-! # Span after taking the actual color projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
variable (R: Submodule ℂ (Label d))
open Push.Mark YM.Source YM.Source.Drops
variable (H:Hol su)(hp:∀ k,Peg H k)(h:Reasons R H)
lemma basis_pay (t:ℝ)(i:ℕ)(p:Pol d): geometry i (pace d t p)=(t:ℂ)^i • geometry i p:=by
     suffices h:(geometry i).comp (pace d t)=(t:ℂ)^i • geometry (d:=d) i from LinearMap.congr_fun h p
     apply (zBasis d).ext; intro j; rw [minted,LinearMap.comp_apply,pace_gen,map_smul,LinearMap.smul_apply,geometry_basis] -- maybe twice
     split
     next h=> rw [h]
     simp only [smul_zero]
lemma tiny (g:Pol d)(G:Push.Mark.Ink su)(W:ℕ)(hw:W=2*(G.1+2))(hW:W≤d)(he: drips W g= coarse d (literal G.2)) : Tendsto (fun i=> (↑((tabula i)^W):ℂ)⁻¹ • setas d (pace d (tabula i) g)) atTop (𝓝 (setas d (coarse d (literal G.2)))):=by
     let s:= (Finset.range (d+1)).filter (W ≤ ·)
     have hz (k:ℕ)(hk:k≤W): geometry k g= if W=k then coarse d (literal G.2) else 0:=by rw [← drips_geom k W g hk,he,crownG, hw]
     have hm(k:ℕ)(h:k≤d): drips d (geometry k g)=geometry k g:= drips_keeps g k h -- prove
     let F(t:ℝ):Mini d:=∑ k∈s, (t:ℂ)^(k-W) • setas d (geometry k g)
     have hf:Continuous F:=continuous_finsetSum _ fun i _=> (Complex.continuous_ofReal.pow (i-W)).smul continuous_const
     have hx(t:ℝ)(h:0<t) : F t=(↑(t^W):ℂ)⁻¹ • setas d (pace d t g):=by
          apply Subtype.ext; change (cap d).subtype (F t)=(↑(t^W):ℂ)⁻¹ • drips d (pace d t g);
          unfold F drips; simp only [map_sum, map_smul,LinearMap.sum_apply,Finset.smul_sum,basis_pay];
          rw [← Finset.sum_subset (Finset.filter_subset (W ≤ ·) (range (d+1)))]; swap -- orientation? maybe rew lhs
          · intro i hi hh; have hv:=lt_of_not_ge (fun h:W ≤ i=> hh (mem_filter.mpr ⟨hi,h⟩)); rw [hz _ hv.le, if_neg hv.ne', smul_zero,smul_zero]
          refine Finset.sum_congr rfl (fun i hi=>?_); obtain ⟨h₁,h₂⟩:=mem_filter.mp hi; change _ • drips d (geometry i g)=_; rw [hm i (by simpa using h₁), Complex.ofReal_pow,smul_smul]; congr 1; have he:(t:ℂ)^i=(t:ℂ)^W*(t:ℂ)^(i-W):= by rw [← pow_add,Nat.add_sub_of_le h₂];
          rw [he,inv_mul_cancel_left₀ (by exact pow_ne_zero _ (by exact_mod_cast h.ne'))] -- arithmetic
     have hh:F 0=setas d (coarse d (literal G.2)):=by
          unfold F; rw [sum_eq_single W]
          · rw [hz W le_rfl, if_pos rfl]; simp
          · intro i hi he; obtain ⟨hx,h₁⟩:=mem_filter.mp hi; simp [show i-W≠0 by omega]
          intro h; exact False.elim (h (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hW),le_rfl⟩))
     rw [←hh]; exact ((hf.tendsto 0).comp tab_zero).congr' (Eventually.of_forall (fun i=>hx _ (rise0 i)))
 where
    drips_keeps (g:Pol d)(i:ℕ)(h:i≤ d): drips d (geometry i g)=geometry i g:=by
       suffices hc:(drips (d:=d) d).comp (geometry i)=geometry i from LinearMap.congr_fun hc g
       apply (zBasis d).ext; intro j; rw [minted, LinearMap.comp_apply, geometry_basis]; split; next hp=> rw [drips_gen,if_pos (hp ▸ h)]
       exact map_zero _
lemma accomodate (p: Pol d)(y:Mini d)(t:ℂ)(z:Pol d) (hz:y= t • setas d z)(j:ℕ)(h :∀ u:Pol d, miniR d (z * pace d (tabula j) u)∈Scales R j) : miniR d (y.val*p)∈Scales R j:=by
      let v:=tabula j; let u:=pace d v⁻¹ p; have he: pace d v u=p:=by unfold u; rw [pace_iter,inv_mul_cancel₀ (rise0 _).ne',pace_launch];
      have hv:setas d (drips d z*p)=setas d (z*p):= Subtype.ext (mulDry_left d d z p)
      rw [hz]; change miniR d ((t • drips d z)*p)∈ _; rw [_root_.smul_mul_assoc,map_smul]; apply Submodule.smul_mem; change brighten d (setas d _)∈ _; rw [hv,← he]; exact h _
lemma warmed (p:Pol d)(h:∀ y:Pol d,miniR d (p*y)∈R)(t:Pol d)(j:ℕ): miniR d (pace d (tabula j) (p*t))∈ Scales R j:=by
   let g:= tabula j; change brighten _ (setas d _)∈ _; rw [← setas_pace, ← pace_color]; exact ⟨_,h t,rfl⟩
include hp h
lemma OreW (G:Push.Mark.Ink su)(hh:Push.Mark.Gap G) (p: Pol d): miniR d (coarse d (literal G.2)*p)∈ crew R :=by
    let W:= 2*(G.1+2); by_cases hW: W ≤ d
    · obtain ⟨g,hg,hY⟩:= OreL (d:=d) H hp G hW hh
      let q:ℕ→Mini d:=fun i=>(↑((tabula i)^W):ℂ)⁻¹ • setas d (pace d (tabula i) g); have hz:= tiny g G W rfl hW hY; let L: Mini d →ₗ[ℂ] Label d:= miniR d ∘ₗ (LinearMap.mulRight ℂ p) ∘ₗ (cap d).subtype; let Φ:= L.toContinuousLinearMap; refine ⟨fun i=>L (q i), ?_, Eventually.of_forall (fun i=>accomodate R p (q i) _ _ rfl i (fun U=>by rw [← race]; exact warmed R g (OreJobs R H h g hg) U i))⟩
      have hv(y:Pol d): L (setas d y)=miniR d (y*p):= congr_arg (brighten d) (Subtype.ext (mulDry_left d d y p)); rw [←hv]; exact (L.continuous_of_finiteDimensional.tendsto _).comp hz -- L maybe args error
    have hj : setas d (coarse d (literal G.2) * p)=0:=by
       apply Subtype.ext; change drips d _=0; rw [← mulDry_left,capital, if_neg hW,zero_mul,map_zero]
    change brighten d (setas d _) ∈crew R; rw [hj,map_zero]; exact Submodule.zero_mem _
omit hp
open Pulses
lemma spinW (l: Letters d) (p:Pol d) : miniR d (flora (Grass.line (petal l))*p)∈ crew R:=by
   obtain ⟨i,j,v⟩:∃ (i:Bool)(w:SpinMode d),leafD i w.1.2.1 w.1.2.2 w.2 w.1.1=l:=by
       cases l with
       | inl t=>exact ⟨false,t,rfl⟩
       | inr t=>exact ⟨true,t,rfl⟩
   obtain ⟨⟨d',j,k⟩,u⟩:=j; obtain ⟨L,hL⟩:=floraL (d:=d); let Φ:= miniR d ∘ₗ mulRight ℂ p ∘ₗ L ∘ₗ (Grass.line (A:=Letters d)); let V:Submodule ℂ (Covec d):= (crew R).comap Φ; have hΦ(y):Φ y=miniR d (flora (Grass.line y)*p):=by change miniR d (L (Grass.line y)*_) = _; rw [hL]
   suffices h:∀ b:Cover, normalD i j k u (vector b)∈ V by
       rw [← v,← hΦ]; exact beamSpan i j k u d' V h
   intro b; let W := normalD (d:=d) i j k u (vector b); let f:=plan (d:=d) i j k u (vector b); let z (n:ℕ):=tabula n^2; let q(n:ℕ):= ((z n):ℂ)⁻¹ • f (z n)
   have h₁(n:ℕ) : 0< z n:= pow_pos (rise0 n) _
   have hg:Tendsto z atTop (𝓝[≠] 0):= tendsto_nhdsWithin_iff.mpr ⟨(by simpa using tab_zero.pow 2),Eventually.of_forall fun n=> (h₁ n).ne'⟩
   have hv:Tendsto q atTop (𝓝 W):=by
       refine (((differs (d:=d) i j k u (vector b)).tendsto_slope_zero).comp hg).congr' (Eventually.of_forall (fun n=>?_)); change (z n)⁻¹ • (f (0+ z n)-f 0)=q n; rw [zero_add,show f 0=0 from plan_zero ..,sub_zero]; ext h; simp [q, Complex.real_smul]
   change Φ W∈crew R; refine ⟨fun i=>Φ (q i), (Φ.continuous_of_finiteDimensional.tendsto _).comp hv, Eventually.of_forall fun n=>?_⟩ -- use fiber actual
   let t:=tabula n; let P:= bent (d:=d) i j k u (fronts b n); let A:=pace d t⁻¹ p; let η:ℂ:= (z n:ℂ)⁻¹; let δ:ℂ:= ((t:ℂ)^3)⁻¹
   have hf:pace d t (flora (Grass.line P))=(t:ℂ)^3 • flora (Grass.line (f (z n))):= by rw [show pace d t _ = _ from plan_t (d:=d) i j k u t (fronts b n)]; rw [pos_front]; -- t reducible? rw
   have hA:pace d t A=p:=by rw [show pace d t A= _ from pace_iter _ _ _,inv_mul_cancel₀ (rise0 _).ne',pace_launch]
   change Φ (η • f (z n))∈_; rw [map_smul,hΦ,← inv_smul_smul₀ (a:=(t:ℂ)^3) (pow_ne_zero _ (by exact_mod_cast (rise0 n).ne')) (flora _),← hf]; rw [_root_.smul_mul_assoc,map_smul,← hA,← race]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (warmed R _ (h.fiber i j k u (fronts b n)) A _))
include hp
open UV.Free
lemma budget : Module.finrank ℂ (ker (@UV.Free.projection d)) ≤ Module.finrank ℂ R:=by
   apply fiscal
   intro p hp'; rw [LinearMap.mem_ker] at hp'; let L:=(crew R).comap (miniR d); have hh:= generative L p.val (show reduceEq p.val=0 from congr_arg Subtype.val hp') (OreW R H hp h) (spinW R H h); change (brighten d (setas d p.val))∈ crew R at hh; rw [← travel,interior] at hh; exact hh
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.budget
