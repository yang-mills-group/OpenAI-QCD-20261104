import YM.Poised.Collage
/-! # Root-native high-order bills for primary -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n m r p w : ℕ}
namespace Counting
open Beacon Next.Foundations Costs Lining Lining.Temper Ferry Merian Sieve Permit Work.G06 Work.G07 Carte Carte.Hem Carte.Cells
open Collage
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
variable (U:Hol su)(A: Exhibit U)
-- sightseeing
namespace Terrain
open Cove Stew Creek
variable {f g:Grid c→Alg (Keys c n)}{a b v :ℝ}{P:BudgetPoint}{o:Site c}{s t:Support c}
lemma padded (p:ℝ)(hp:a≤p)(hh:Sight s o k P v f a) : Sight s o k P v f p:= ⟨hh.room,hh.gate,hh.use,fun i h l he ht=>(hh.pole i h l he ht).trans hp,hh.borel,hh.travels.trans hp⟩
lemma zeroL : Sight s o k P v (0: Grid c→Alg (Keys c n)) 0:=by
    refine ⟨fun _ _ _=> rfl, fun _=>Subalgebra.zero_mem _,fun _ _=>contDiffAt_const, fun i h l he ht=> ?_,measurable_const,rfl.le⟩; rw [show RG.leftDerivs (0: Grid c→Alg (Keys c n)) l i=0 from ?_]; swap; · simpa only [ite_self] using! left_const (0:Alg (Keys c n)) l i
    simp [view]
lemma visitG (f g: Alg (Keys c n))(o: Site c)(k:ℕ) (hv:0≤v): view o k (f+g) v ≤ view o k f v+view o k g v:=by unfold view; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; rw [map_add,← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (by unfold toll; positivity)
lemma persuaded (hf:Sight s o k P v f a)(hg:Sight s o k P v g b)(hv:0≤v): Sight s o k P v (f+g) (a+b):=by
   refine ⟨fun i j hw=> congr_arg₂ (·+·) (hf.room i j hw) (hg.room i j hw), fun i=>Subalgebra.add_mem _ (hf.gate i) (hg.gate i), fun i h=>(hf.use i h).add (hg.use i h), fun i h l he ht=> ?_,hf.borel.add hg.borel,add_nonneg hf.travels hg.travels⟩; rw [Push.Local.left_add l (hf.use i h) (hg.use i h) he]; exact (visitG _ _ o k hv).trans (add_le_add (hf.pole i h l he ht) (hg.pole i h l he ht)) -- syntax
lemma viatic (t:ℂ)(f:Alg (Keys c n))(o:Site c)(k:ℕ)(v:ℝ): view o k (t • f) v = ‖t‖*view o k f v:=by unfold view; rw [mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,norm_smul, mul_left_comm]
lemma scaledL (hf:Sight s o k P v f a)(r:ℂ): Sight s o k P v (r • f) (‖r‖*a):=by
    refine ⟨fun i j hk=> congr_arg (r • ·) (hf.room i j hk),fun i=>Subalgebra.smul_mem _ (hf.gate i) _,fun i h=>by
        let g:= ((r • (LinearMap.id : Alg (Keys c n)→ₗ[ℂ]Alg (Keys c n))).restrictScalars ℝ).toContinuousLinearMap; exact g.contDiff.contDiffAt.comp (f:=f∘increment i) 0 (hf.use _ h),fun i h l he ht=> ?_,hf.borel.const_smul _,mul_nonneg (norm_nonneg _) hf.travels⟩
    let g:= ((r • (LinearMap.id : Alg (Keys c n)→ₗ[ℂ]Alg (Keys c n))).restrictScalars ℝ).toContinuousLinearMap; change view o k (RG.leftDerivs (g∘f) l i) v ≤ _; rw [Push.Local.left_linear g l (hf.use i h) he]; change view o k (r • _) _≤_; rw [viatic]; exact mul_le_mul_of_nonneg_left (hf.pole i h l he ht) (norm_nonneg _)
lemma series {I:Type*}(i:Finset I)(f:I→ Grid c→Alg (Keys c n))(u:I→ℝ)(h:∀ j∈i,Sight s o k P v (f j) (u j))(hv:0≤v): Sight s o k P v (∑ j∈i,f j) (∑ j∈i,u j):=by
    induction i using Finset.induction_on with |empty=> rw [sum_empty,sum_empty]; exact zeroL|insert i j hi ih=> rw [sum_insert hi,sum_insert hi]; exact persuaded (h i (mem_insert_self ..)) (ih fun k hk=>h k (mem_insert_of_mem hk)) hv
lemma shelf_out (ht:s⊆t)(h:Sight s o k P v f a): Sight t o k P v f a:=⟨fun i j hp=>h.room i j (agrees_mono hp ht),fun i=> (QCD.Creek.regionMon (Cove.limitsMon s t ht)) (h.gate i),fun i hi=> h.use _ (hi.mono_left ht),fun i hi=>h.pole i (hi.mono_left ht),h.borel,h.travels⟩ -- syntax
end Terrain
namespace Click
local notation "I"=>Pairs (Modes c 6)
abbrev cField (c:Side)(b:Cover)(d:ℕ)(x:Pol d)(V:Grid c): Lat.Fields c 6:= perigee c b (A.t d) (glaze (A.F d) (A.U d) (A.t d) (expandAt (wrap c b) V) x)
lemma cartridge (c:Side)(b:Cover)(V:Grid c)(x:Label d): Realize.placed (A.t d) c b (A.lead d x) V=cField U A c b d x.val V:=by rw [Realize.location,places]; unfold Cylinder.evaluate; change adapter _ _ (porch _ _ _) = _; rw [A.label]; rfl
-- stage.Price.R canonical output for meter. no threshold comparator for supports.
open Cells
local notation "T₀"=> A.t d
local notation "T"=>Nearest (A.t d) 6
local notation "N"=> Pairs T
lemma tentT (x:PowerPair d)(he: Permit.used_bound (A.t d) r)(m k n:ℕ): ∃ t:ℝ,0≤t ∧ ∀(b:Cover)(B:BudgetPoint)(c:Side), B.power=m → B.order=k→2*(r+1)<c.val → ∀ v:ℝ,0<v → Sight (pot (r+1) c b) (wrap c b) n B v (cField U A c b d (gen x)) (t* B.threshold^(life x.1)*v^x.2.card):=by
    obtain ⟨C,hC,h⟩:= copay U A x he k m
    have ht:0≤(1+(r:ℝ))^n:=by positivity
    refine ⟨C*(1+(r:ℝ))^n,mul_nonneg hC ht,fun b B c hl hm hh v hx=> ?_⟩; let L:= listing U A x; let o:=wrap c b; let f:= L∘expandAt o; have hL:= h B c o hh hl
    let M:= ((tongue (c:=c) T₀ b).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; have he' : cField U A c b d (gen x)=M ∘ f:=rfl
    rw [he']; have hX:LocalOn ((A.t d).image (fun i=>wrap c i + o)) f:=by simp only [Finset.coe_image]; exact LocalOn.expandAt (T₀:Set Cover) L (listing_floor U A x) o
    have h' : pot r c b⊆pot (r+1) c b:= Corona.halo_mono (by omega) (Finset.Subset.refl _); have hw (V:Grid c): Push.Local.Chart B.order f V:=(hL.smooth [] (Nat.zero_le k) V).contDiffAt.of_le (by norm_cast; simp)
    have hB : LocalOn (pot (r+1) c b) f:= fun i j hj=> hX _ _ (agrees_mono hj (halos T₀ (r+1) (by omega : r ≤ r+1) o he))
    refine ⟨fun i j hp=>congr_arg M (hB i j hp),fun i=>Creek.regionMon (Cove.limitsMon _ _ h') (ranch _ b (f i) he),fun i _=> M.contDiff.contDiffAt.comp _ (hw _),fun i hi l hp ho=> ?_,M.continuous.measurable.comp (((listedC U A x).comp (show Continuous (expandAt o (K:=su.El)) from by unfold expandAt; fun_prop)).measurable),by positivity [B.threshold_pos]⟩ -- replace Gate
    rw [Push.Local.left_linear M l (hw i) hp]; let y:=RG.leftDerivs f l i
    have hκ:y∈layer N x.2.card:=by
        -- linear map mark grade left
        let P:= ((Stew.panel (D:=N) x.2.card).restrictScalars ℝ).toContinuousLinearMap
        have hv : P∘f=f:=funext fun i=> (Stew.past x.2.card x.2.card (porch_part U A x (expandAt o i))).trans (if_pos rfl)
        have ht : P y=y:=by unfold y; rw [← Push.Local.left_linear P l (hw i) hp,hv]
        rw [← ht]; exact Stew.chamber x.2.card y
    have ht' := hL.bound l (hm ▸ hp) ho i hi; rw [one_pow, mul_one] at ht'
    exact (pennyT T₀ b n y he v hx hκ).trans ((mul_le_mul_of_nonneg_left ht' (by positivity)).trans_eq (by ring))
variable (θ v:ℝ)
abbrev reaches (x:Pol d) (p:PowerPair d):ℂ := (zBasis d).repr x p
def chair (d:ℕ): Finset (PowerPair d) := (weightFinite d).toFinset
lemma atBasis (x: Label d): x.val=∑ i∈chair d,reaches x.val i • gen i:=by
    let f:= (zBasis d).repr x.val; have h:x.val= ∑ i∈f.support,f i • gen i:=by simp_rw [← minted]; exact ((zBasis d).linearCombination_repr x.val).symm
    apply Eq.trans h (sum_subset _ (fun p h H=>by rw [show f p=0 from Finsupp.notMem_support_iff.mp H,zero_smul])); intro p hp; apply (Set.Finite.mem_toFinset _).mpr; have ht:reaches x.val p≠0:= Finsupp.mem_support_iff.mp hp
    by_contra hG; apply ht; have hv(i:Pol d) (h:i∈ UV.cap d) : reaches i p=0:=by
       apply Submodule.span_induction (p:=fun i _=> reaches i p=0) ?_ ?_ ?_ ?_ h
       · rintro i ⟨i,hi,rfl⟩; have he:i≠p:= fun hh=> hG (hh ▸ hi); unfold reaches; rw [← minted]; simp [he,he.symm]
       · rw [reaches,map_zero]; rfl
       · intro i j _ _; unfold reaches; rw [map_add,Finsupp.add_apply]; intro hi hj; rw [hi,hj,add_zero]
       intro i j _; unfold reaches; rw [map_smul,Finsupp.smul_apply]; intro hj; rw [hj,smul_zero]
    exact hv x.val ((label_law _).1 x.property).1
lemma dim_basis (x:Label d)(p: PowerPair d) : reaches (dimming θ v d x).val p= (θ:ℂ)^life p.1*(v:ℂ)^p.2.card*reaches x.val p:=by
    change ((zBasis d).coord p) (widths θ v x.val) = (θ:ℂ)^life p.1*(v:ℂ)^p.2.card*((zBasis d).coord p) x.val; suffices h : ((zBasis d).coord p).comp (widths θ v)=( (θ:ℂ)^life p.1*(v:ℂ)^p.2.card) • (zBasis d).coord p from DFunLike.congr_fun h x.val
    apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted,widths_m,map_smul, ← minted]; by_cases he:p=i <;> simp [he,Ne.symm]
lemma assembleT (c:Side)(b: Cover) (x:Label d): (fun i=> Realize.placed (A.t d) c b (A.lead d x) i)=∑ i∈chair d,reaches x.val i • cField U A c b d (gen i):=by
    funext V; rw [Finset.sum_apply,cartridge]; conv_lhs=>rw [atBasis x]
    unfold cField; rw [map_sum]; unfold perigee; rw [map_sum]; simp_rw [map_smul]; rfl
open Module
lemma wide (F:Basis (Fog d) ℂ (Label d)) (he: Permit.used_bound (A.t d) r)(m k n:ℕ): ∃ t:ℝ,0≤t ∧ ∀(b:Cover)(B:BudgetPoint)(c:Side), B.power=m → B.order=k→2*(r+1)<c.val → ∀ v:ℝ,0<v →∀ x:Label d, Sight (pot (r+1) c b) (wrap c b) n B v (fun i=>Realize.placed (A.t d) c b (A.lead d x) i) (t*watch F x B.threshold v):=by
   choose C hC H using fun x:PowerPair d=> tentT U A x he m k n
   let L (x:PowerPair d) : (Fog d→ℂ) →ₗ[ℂ] ℂ := ((zBasis d).coord x).comp ((labels d).subtype.comp F.equivFun.symm.toLinearMap)
   obtain ⟨g,hg,hW⟩ : ∃ g:PowerPair d→ℝ,(∀ x,0≤g x) ∧ ∀ x i, ‖L x i‖ ≤ g x*‖i‖:=by
      choose C h H using fun x=> clm_fee (L x); exact ⟨C,h,H⟩
   refine ⟨∑ i∈chair d,C i*g i, Finset.sum_nonneg (fun _ _=>mul_nonneg (hC _) (hg _)),fun b B c hK hδ hN v hv x=>?_⟩
   rw [assembleT]; apply Terrain.padded _ _ (Terrain.series _ _ _ (fun i _=>Terrain.scaledL (H i b B c hK hδ hN v hv) (reaches x.val i)) hv.le); rw [Finset.sum_mul]; refine Finset.sum_le_sum fun p _=> ?_; let θ:= B.threshold; let y:= cose F (dimming θ v d x)
   have ht : θ^life p.1*v^p.2.card*‖reaches x.val p‖ ≤ g p*‖y‖:= by
       have hp:L p y=reaches (dimming θ v d x).val p:=by change reaches (F.equivFun.symm (F.equivFun _)).val p=_; rw [F.equivFun.symm_apply_apply]
       have h:= hW p y; rw [hp,dim_basis, norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hv.le,Real.norm_of_nonneg B.threshold_pos.le] at h; exact h
   unfold θ at ht; exact le_trans (le_of_eq (b:=C p*(B.threshold^life p.1*v^p.2.card*‖reaches x.val p‖)) (by ring)) ((mul_le_mul_of_nonneg_left ht (hC p)).trans_eq (mul_assoc ..).symm)
 where clm_fee {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E](L:E→ₗ[ℂ]ℂ):∃ C:ℝ,0≤C∧∀ x,‖L x‖ ≤ C*‖x‖:=⟨_,norm_nonneg (L.toContinuousLinearMap),fun x=> L.toContinuousLinearMap.le_opNorm x⟩
end Click
end Counting
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Counting.Click.wide
