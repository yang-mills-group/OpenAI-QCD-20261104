import YM.Elms.Braze
/-! # Start replicated equation discrepancies with unweighted fortunes -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate
open Cove Creek Stamp
variable {Y:SourceRead.TaperHol}{p:Label d}(V:Knot p)(h:Requisite Y p V)
include h
local notation "Ψ" q:arg l:arg=>evoc q l
lemma measuresC (l:List Axis): ∃ C:ℝ,0≤C ∧ ∀ᶠ r:ℕ in atTop,∀ k m d₀ j:ℕ,∃ D:ℝ,1≤D∧∀ (O:BudgetPoint)(K:Side)(b:Cover)(P:Regulator K 6)(v:ℝ),0<v→ P.t=0→O.order=k→ O.power=m→2*(r+1)< K.val→ |V.c P| * levy V.m V.t O.threshold v ≤ levy V.g V.s O.threshold v → (let H:= evoc (V.tool P) l K b; let α:= (levy V.g V.s O.threshold v)⁻¹; Flame ⇑((α:ℂ) • H) O (pot (r+1) K b) (wrap K b) v d₀ j D∧∀ U:Grid K,Creek.load (fun _=>v) (((α:ℂ) • H :Insertion K 6) U) ≤ C*((O.threshold^V.g)⁻¹+(O.threshold^V.m)⁻¹)) :=by
    obtain ⟨C,hC,hZ⟩:=uproot (evoc V.X l) (evoc V.Y l) _ _ _ _ (crestBorn _ (spoke h.mantle l)) (crestBorn _ (spoke h.rent l)); refine ⟨C,hC,?_⟩; filter_upwards [hZ] with r hr k m d j; obtain ⟨D,hD,hX⟩:=hr k m d j; refine ⟨D,hD,fun O K b P v hv hp hk hm hz hx=>?_⟩; rw [lawEv P h]; exact hX O K b v (V.c P) hv hk hm hz hx -- shadow
lemma angleRoof (l:List Axis)(n:Side)(P:Regulator n 6)(x y: Cover): Patria.march y (evoc (V.tool P) l n x)= evoc (V.tool P) l n (x+y):=by
    rw [lawEv P h]; let f:= evoc V.X l; let Z:= evoc V.Y l; let v:ℂ:= (V.c P:ℂ); have hx:= shiftCorrespond f (spoke h.mantle l); have hZ:= shiftCorrespond Z (spoke h.rent l); funext U; change march y (fun U:Grid n=> f n x U+v • Z n x U) U=f n (x+y) _+v • Z n (x+y) _;
    apply Eq.trans (cane f Z x v y U) (congr_arg₂ (·+·) (congr_fun (hx n x y) U) (congr_arg (v • ·) (congr_fun (hZ n x y) U)))
 where
   cane(f Z:Drape)(x:Cover)(v:ℂ)(y:Cover)(U:Grid n): Patria.march y (fun U:Grid n=> f n x U+v • Z n x U) U=march y (f n x) U+v • march y (Z n x) U:=by
       unfold march TorusPCAC.Geometry.post; simp
lemma otherW : ∃ y:Label d, TravelsP Y V.Y (passport d y):=by obtain ⟨K⟩:= Source.Hol.exists_ode su; exact rover Y K _ _ _ _ h.hasy h.rent
omit h
noncomputable abbrev tiara (O:BudgetPoint)(v:ℝ) (X Y:Label d) : Label d := (↑(levy V.g V.s O.threshold v):ℂ)⁻¹ • (X+(V.c P:ℂ) • Y)
lemma transferQ(d:ℕ) (t v:ℝ)(y:Label d):prism t v d (passport d y)=passport d (dimming t v d y):=by apply Subtype.ext; rw [measures]; rfl
lemma bank (d:ℕ):Injective (passport d):= Submodule.inclusion_injective _
lemma deposit (X:Drape)(p:Label d)(d' g s:ℕ)(hX:X∈ phrase g s)(hp:TravelsP Y X (passport d p))(v t:ℝ): dimming t v d p = (v:ℂ)^s • dimming t 1 d p:=by
    obtain ⟨N,hp⟩:=hp; let n:Side:=⟨N+1,Nat.succ_pos _⟩; have hx:=crestBorn X hX
    have h:= sizedSpin (0:Cover) Y X (passport d p) s g hx (fun n o U=>convoy hx U o) (hp n 0 (by change N≤N+1; omega)) v t
    simp_rw [transferQ] at h; exact bank d (by rw [map_smul]; exact h)
include h
lemma ledger (X:Label d)(hp:TravelsP Y V.X (passport d X)) : Tendsto (fun t:ℝ=> ((↑(t^V.g):ℂ))⁻¹ • dimming t 1 d X) (𝓝[>] 0) (𝓝 p):=by
    obtain ⟨q,⟨M,hM⟩,hw⟩:=typedW Y p V h; obtain ⟨N,hN⟩:=hp; let n:Side:=⟨N+M+1,Nat.succ_pos _⟩; have ht:X=q:=Subtype.ext (Poised.Beacon.chooses Y 0 (Submodule.coe_mem (passport d X)) (Submodule.coe_mem (passport d q)) (hN n 0 (by change _≤N+M+1; omega)) (hM n 0 (by change _ ≤ N+M+1; omega))); -- _ implicit mem solve
    have hi:=LinearMap.exists_antilipschitzWith (passport d) (LinearMap.ker_eq_bot.mpr (bank d)); obtain ⟨L,hL,h⟩:=hi; rw [ht]; refine ((h.isEmbedding (passport d).continuous_of_finiteDimensional).isInducing.tendsto_nhds_iff).mpr ?_; exact hw.congr' (Eventually.of_forall fun i=> by simp [Function.comp_apply,transferQ]) -- simp direction
lemma princip (X Z:Label d)(hf:TravelsP Y V.X (passport d X))(hz:TravelsP Y V.Y (passport d Z)): ∀ ε:ℝ,0<ε→ ∃ δ γ:ℝ,0<δ∧ γ>0 ∧∀(n:Side)(P:Regulator n 6)(O:BudgetPoint)(v:ℝ),O.threshold <γ →0<v→|V.c P| * levy V.m V.t O.threshold v ≤ δ* levy V.g V.s O.threshold v→ ‖dimming O.threshold v d (tiara P V O v X Z) - p‖<ε:=by
    let ℱ:=fun t:ℝ=> ((↑(t^V.g):ℂ))⁻¹ • dimming t 1 d X; let L:=(𝓝[>] (0:ℝ)); intro ε hε; obtain hm:= ledger V h X hf; let F(t:ℝ):= ((↑(t^V.m):ℂ))⁻¹ • dimming t 1 d Z
    -- Need bounded threshold launch for weaker Poll: know via lease_flame/hx costs. No compact? polynomial θ scaled using Leaf lease.P.Engine or Survey for Y not guaranteed? Shelf h.rent (phase g,t) implies Survey y dims EXISTS.R because phrase generation.Pivot survey each mon.L. Yes.
    have hC :∃ D:ℝ,0<D∧∀ᶠ t:ℝ in L,‖F t‖ < D:=by
       obtain ⟨K⟩:= Source.Hol.exists_ode su; have hP:Peg K (d/2):= Work.G02.answer Work.G01.answer su K _
       have hp:=h.rent; have hw : ∀ x∈phrase V.m V.t,∃ q:Mini d, Survey Y x V.m V.t q:=by
         intro x h; refine Submodule.span_induction ?_ ?_ ?_ ?_ h; rintro x ⟨l,rfl,hy,hr⟩; rw [←hy,←hr]; exact ⟨_,leaves Y K l hP⟩
         · exact ⟨_,Survey.dry Y V.m V.t d⟩
         · rintro x y _ _ ⟨z,hz⟩ ⟨p,hp⟩; exact ⟨_,hz.add hp⟩
         rintro u y _ ⟨z,hz⟩; exact ⟨_, hz.scale u⟩
       obtain ⟨f,hF⟩:=hw _ hp; obtain ⟨a,⟨N,hN⟩,hx⟩:=hF.grantX; obtain ⟨M,hM⟩:=hz; let n:Side:=⟨N+M+1,Nat.succ_pos _⟩; rw [show a= passport d Z from Subtype.ext (Poised.Beacon.chooses Y 0 (Submodule.coe_mem a) (Submodule.coe_mem _) (hN n 0 (by change N≤N+M+1; omega)) (hM n 0 (by change M≤N+M+1; omega)))] at hx; simp_rw [transferQ] at hx -- rw binder
       let S:= ((passport d).leftInverse).toContinuousLinearMap; have hv : Tendsto F L (𝓝 (S f)):=by
          refine ((S.continuous.tendsto f).comp hx).congr' (Eventually.of_forall fun i=>?_); unfold F; simp_rw [Function.comp_apply,←map_smul (passport d)]; exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (bank d)) _
       exact ⟨‖S f‖+1,by positivity,hv.norm.eventually (gt_mem_nhds (lt_add_one ..))⟩ -- `lt_add_one` real
    obtain ⟨D,hD,hC⟩:=hC; let e:= ε/2; let δ:=e/D; have he:0<e:=half_pos hε; have hh:δ*D=e:= div_mul_cancel₀ _ hD.ne'; have hd:0<δ:=div_pos he hD
    obtain ⟨γ,hV,hZ⟩ : ∃ γ:ℝ,0<γ ∧ Metric.ball 0 γ∩ Set.Ioi (0:ℝ) ⊆ {i | dist (ℱ i) p<e ∧ ‖F i‖ < D} := Metric.mem_nhdsWithin_iff.mp ((Metric.tendsto_nhds.mp hm e he).and hC); refine ⟨δ,γ,hd,hV,?_⟩; intro n P O v hv ht hζ; let t:= O.threshold; have h0:0<t:=O.threshold_pos; have hr: t∈ Metric.ball 0 γ:=by rw [Metric.mem_ball, Real.dist_eq, sub_zero,abs_of_pos h0]; exact hv
    let M:= levy V.g V.s t v; let M':= levy V.m V.t t v; have hj:0<M:=by unfold M levy; positivity
    have hmθ: 0<M':=by unfold M' levy; positivity
    let g:= V.c P; have hx:dimming t v d (tiara P V O v X Z)=ℱ t+(↑(g*M'/M):ℂ) • F t:=by
       unfold tiara ℱ F; simp only [map_add,map_smul,smul_add]; rw [deposit V.X X 0 V.g V.s h.mantle hf v t,deposit V.Y Z 0 V.m V.t h.rent hz v t]; -- hZ hz shadow
       simp only [smul_smul]; apply congr_arg₂ (·+·)
       · apply congr_arg (· • _); simp only [t,levy, Complex.ofReal_mul, Complex.ofReal_pow]; field_simp [show (O.threshold:ℂ)≠0 from (by exact_mod_cast O.threshold_pos.ne'), show (v:ℂ) ≠0 from (by exact_mod_cast ht.ne')]
       apply congr_arg (· • _); unfold t at h0; unfold g M M' t levy; simp only [Complex.ofReal_mul, Complex.ofReal_pow,Complex.ofReal_div]; field_simp [show (O.threshold:ℂ)≠0 from (by exact_mod_cast O.threshold_pos.ne'),show (v:ℂ)≠0 from (by exact_mod_cast ht.ne')] <;> ring
    obtain ⟨h1,h2⟩:=hZ ⟨hr,h0⟩; change dist (ℱ t) p<e at h1; rw [dist_eq_norm] at h1; change ‖dimming t v _ _-_‖<_; rw [hx,add_sub_right_comm]; apply (norm_add_le ..).trans_lt; rw [norm_smul, Complex.norm_real,Real.norm_eq_abs]; have hz: |g*M'/M|≤δ:=by rw [abs_div,abs_mul,abs_of_pos hj, abs_of_pos hmθ, div_le_iff₀ hj]; exact hζ
    exact (add_lt_add_of_lt_of_le h1 (mul_le_mul hz (show ‖F t‖ < D from h2).le (norm_nonneg _) hd.le)).trans_eq (by rw [hh]; exact add_halves _)
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
