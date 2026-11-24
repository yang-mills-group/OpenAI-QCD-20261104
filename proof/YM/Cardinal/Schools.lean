import YM.Poised.Caps
import YM.Cardinal.Ear
/-! # inertia of label grades and cost basis. Primal, not project away masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {a b t θ v:ℝ}{k d n j:ℕ}{c:Side}
open Pipes Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets
-- Kernel-preserving grading. coefficient norms raw.
abbrev Grade := ℕ×ℕ×ℕ
noncomputable def crest (p:PowerPair d): Grade:= (UV.weight p, life p.1, p.2.card)
local notation "w"=>UV.weight
local notation "G'"=> Grade
variable {u:su.El}
lemma incidents (i j:PowerPair d)(p:su.El)(h:coord j (colorAct p (gen i))≠0): crest i=crest j:=by
    let W:=w i; let x:=colorAct p (gen i); have hX:x=geometry W x:=by
       rw [←luminousG, geometry_basis, if_pos rfl]
    have hW:w j=W :=by by_contra ht; exact h (show coord _ x=0 from (congr_arg (coord j) hX).trans ((geo_basis j x W).trans (if_neg ht)))
    have ht (a b:ℝ): ((a:ℂ)^life i.1*(b:ℂ)^i.2.card) • coord j x = ((a:ℂ)^life j.1*(b:ℂ)^j.2.card)*coord j x:=by
       have hv: widths a b x=((a:ℂ)^life i.1*(b:ℂ)^i.2.card) • x:=by rw [← colorWidth, widths_m,map_smul];
       rw [← map_smul (coord j), ← hv, rank_fee]
    have hζ(a b:ℝ): (a:ℂ)^life i.1*(b:ℂ)^i.2.card= (a:ℂ)^life j.1*(b:ℂ)^j.2.card:=mul_right_cancel₀ h (ht a b) -- defeq x
    have he(m n:ℕ)(h:(2:ℂ)^m=(2:ℂ)^n):m=n:= StrictMono.injective (pow_right_strictMono₀ (show 1<(2:ℝ) by norm_num)) (by exact_mod_cast h)
    exact Prod.ext hW.symm (Prod.ext (he _ _ (by simpa [crest] using hζ 2 1)) (he _ _ (by simpa [crest] using hζ 1 2)))
noncomputable def kind (d:ℕ) (s:Grade):Pol d→ₗ[ℂ]Pol d:= (zBasis d).constr ℂ (fun i:PowerPair d=> if crest i=s then gen i else 0)
lemma kind_gate (s:Grade)(i:PowerPair d): kind d s (gen i)= if crest i=s then gen i else 0:=by nth_rw 1 [← minted i]; exact Module.Basis.constr_basis ..
lemma kind_S (s:Grade)(i:PowerPair d)(x:Pol d): coord i (kind d s x)= if crest i = s then coord i x else 0:=by
   have hp:(coord i).comp (kind d s)= if crest i=s then coord i else 0:=by
      apply (zBasis d).ext; intro j; rw [minted,LinearMap.comp_apply,kind_gate]; by_cases he:i=j
      · subst j; split; · rfl
        next h=> exact map_zero _
      have hv: coord i (gen j)=0:=by rw [coord,←minted]; simp [he]
      split_ifs <;> first | exact hv | exact (map_zero _).trans hv.symm | exact map_zero _ | rfl -- simp
   change ((coord i).comp (kind d s)) x= _; rw [hp]; split <;> rfl
lemma kind_t (s:Grade)(p:su.El)(x:Pol d): kind d s (colorAct p x)=colorAct p (kind d s x):=by
    suffices h:(kind d s).comp (colorAct p)=(colorAct p).comp (kind d s) from DFunLike.congr_fun h x
    apply (zBasis d).ext; intro i; rw [minted,LinearMap.comp_apply,LinearMap.comp_apply,kind_gate]; apply (zBasis d).repr.injective; ext j; change coord j _=coord j _ ; rw [kind_S]; by_cases he:coord j (colorAct p (gen i))=0; · split_ifs <;> first | exact he.symm | rw [he,map_zero,map_zero] | rw [map_zero,map_zero] | rfl
    rw [incidents i j p he]; split <;> simp_all
lemma kind_keeps(s:Grade)(x:Label d): kind d s x.val∈labels d:=by
    obtain ⟨h,hv⟩:= (label_law _).mp x.property; apply (label_law _).mpr ⟨?_,fun k=>by rw [←kind_t,hv]⟩
    rw [atBasis x,map_sum]
    apply Submodule.sum_mem; intro i hi; rw [map_smul,kind_gate]; split; next h=>exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,(Set.Finite.mem_toFinset _).mp hi,rfl⟩)
    next _=>rw [smul_zero]; exact Submodule.zero_mem _
noncomputable def gradeCut (d:ℕ)(s:Grade):Label d→ₗ[ℂ]Label d:= ((kind d s).comp (labels d).subtype).codRestrict _ (kind_keeps s)
-- index
noncomputable def gradeS (d:ℕ) := (chair d).image crest
noncomputable abbrev Jars (d:ℕ):= ↥(gradeS d)
lemma sumCut (x:Label d): ∑ i:Jars d,gradeCut d i.val x=x:=by
    apply Subtype.ext; apply (zBasis d).repr.injective; ext i; change coord i ((labels d).subtype (∑ j:Jars d, gradeCut d j.val x)) = coord i x.val; rw [map_sum,map_sum]; change ∑ j:Jars d, coord i (kind d j.val x.val)= coord i x.val; simp_rw [kind_S]
    by_cases h:coord i x.val=0; · simp [h]
    let u:Jars d:=⟨crest i,mem_image_of_mem _ (menu x.val ((label_law _).mp x.property).1 i h)⟩; rw [sum_eq_single u,if_pos rfl]; · intro b hb hv; exact if_neg fun he=> hv (Subtype.ext he.symm)
    simp
lemma cut_afford (x:Label d)(s:Jars d): Facets.Saturated (gradeCut d s.val x).val s.val.1 s.val.2.1 s.val.2.2:=by
   constructor; intro p hp; have h:crest p=s.val:=by_contra fun h=> hp ((kind_S s.val p x.val).trans (if_neg h))
   exact ⟨congr_arg Prod.fst h,congr_arg (Prod.fst∘ Prod.snd) h,congr_arg (Prod.snd∘ Prod.snd) h⟩
-- parity.G.Actor preserved. Mood
variable (q:Bool)
noncomputable def gammaQ (q:Bool):ℂ:= if q then -1 else 1
abbrev moored (x:Pol d)(q:Bool):Prop:= parityAct x=gammaQ q • x
lemma profile_i (s:Grade)(x:Pol d): parityAct (kind d s x)=kind d s (parityAct x):=by
   suffices h:parityAct.comp (kind d s)=(kind d s).comp parityAct from DFunLike.congr_fun h x
   apply (zBasis d).ext; intro i; rw [minted,LinearMap.comp_apply, LinearMap.comp_apply, kind_gate]
   have h:parityAct (gen i)= (-1:ℂ)^i.2.card • gen i:= by unfold parityAct gen; rw [TensorProduct.map_tmul]; change _⊗ₜ[ℂ]Grass.grade _=_; rw [Grass.grade_mono]; exact TensorProduct.tmul_smul .. -- signature
   rw [h,map_smul,kind_gate]; split_ifs; exact h; rw [map_zero,smul_zero]
lemma invites (s:Grade)(x:Label d)(hp:moored x.val q) : moored (gradeCut d s x).val q:=by change parityAct (kind d s x.val)=_; rw [profile_i,hp,map_smul]; rfl
-- grade floor.H.an.E.P.
lemma jar_w (s:Jars d): s.val.1 ≤ d:=by
    obtain ⟨i,hi,hp⟩:= mem_image.mp s.property; rw [← hp]; exact (Set.Finite.mem_toFinset (weightFinite d)).mp hi
-- Relative weighted estimates via components. L∞ to ℓ1.P.Condition.Payn
noncomputable def wealth (x: Pol d)(t v:ℝ) := ∑ i:Rings d, ‖fare i.val x t v‖
lemma wealth_ge (x:Pol d)(t v:ℝ):0≤ wealth x t v:= sum_nonneg fun _ _=>norm_nonneg _
lemma fare_cap (p:Rings d)(x:Pol d)(t v:ℝ): ‖fare p.val x t v‖ ≤ wealth x t v:=single_le_sum (f:=fun i:Rings d=>‖fare i.val x t v‖) (fun _ _=>norm_nonneg _) (mem_univ p)
lemma size_ν (s:Grade)(x:Pol d)(p:Rings d)(t v:ℝ): fare p.val (kind d s x) t v= if crest p.val=s then fare p.val x t v else 0:=by unfold fare; simp_rw [rank_fee,kind_S]; split; rfl; rw [mul_zero]
lemma coinsS (x:Label d)(t v:ℝ): wealth x.val t v= ∑ i:Jars d, wealth (gradeCut d i.val x).val t v:=by
   unfold wealth; rw [sum_comm]; apply sum_congr rfl; intro i _; simp_rw [show ∀ j:Jars d, (gradeCut d j.val x).val= kind d j.val x.val from fun _=>rfl,size_ν]
   let s:Jars d:= ⟨crest i.val,mem_image_of_mem _ i.property⟩; rw [sum_eq_single s,if_pos rfl]; · intro b hb hh; rw [if_neg (fun he=> hh (Subtype.ext he.symm)),norm_zero]
   simp
lemma use_coal (x: Label d)(ht:0<t)(hv:0<v)(hx:wealth x.val t v=0): x=0:=by
    apply Subtype.ext; apply (zBasis d).repr.injective; ext i; change coord i x.val=coord i (0:Pol d); rw [map_zero]; by_contra h; let u:Rings d:= ⟨i, menu x.val ((label_law _).mp x.property).1 _ h⟩
    have hz:coord u.val (widths t v x.val)=0:= norm_le_zero_iff.mp ((fare_cap u x.val t v).trans_eq hx); rw [rank_fee] at hz; exact ((mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht.ne')) (pow_ne_zero _ (by exact_mod_cast hv.ne'))) h) hz)
lemma payFrame (F₀: Basis (Fog d) ℂ (Label d)):∃ C:ℝ,1≤ C ∧∀ (x:Label d)(t v:ℝ), watch F₀ x t v ≤ C*wealth x.val t v:=by
    let f: (Fog d→ℂ)→ₗ[ℂ]Rings d→ ℂ := LinearMap.pi (fun i:Rings d=> (coord i.val).comp ((labels d).subtype.comp F₀.equivFun.symm.toLinearMap))
    let F (i:Rings d) := (((LinearMap.proj (R:=ℂ) (φ:=fun _:Rings d=>ℂ) i).comp f).toContinuousLinearMap).restrictScalars ℝ
    have he(x:Fog d→ℂ)(hp:∀ i,F i x=0):x=0:=by
         let y:= F₀.equivFun.symm x; have hy: guide y.val=0:= funext fun i=> hp i; have hg:y=0:= Subtype.ext (show y.val=0 from (Stative.quiet _ ((label_law _).mp y.property).1).symm.trans ((congr_arg (Stative.line d) hy).trans (map_zero _))); exact F₀.equivFun.symm.injective (hg.trans (map_zero _).symm)
    obtain ⟨C,hC,H⟩:= budget_probes F he (fun _=>1) fun _=>zero_le_one -- context lacks designated type? arguments norms as 𝕜=R
    exact ⟨max 1 C,le_max_left ..,fun x t v=> (H _ (wealth_ge x.val t v) (F₀.equivFun (dimming t v d x)) fun i=>by rw [one_mul]; apply le_trans _ (fare_cap i x.val t v); rw [show F i _=coord i.val (F₀.equivFun.symm _).val from rfl, LinearEquiv.symm_apply_apply]; rfl).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (wealth_ge x.val t v))⟩
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.kind_t
