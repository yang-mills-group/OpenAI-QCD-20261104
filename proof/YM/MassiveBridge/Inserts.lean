import YM.MassiveBridge.Slab

/-!
# The actual Slabs assumption purchases the operator bounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Analysis
open Fields (distinct prepend pointMoment)
open OS (Cross)
open scoped Topology NNReal BigOperators ContDiff InnerProductSpace ComplexOrder
variable {F : Fields} {S : F.Kernel} {a : Axis} {d e : ℝ≥0}

-- Linearity without commuting any fields
lemma clusterEq (l r : Cluster F) : l++r=realize (Fin.append (tokens l) (tokens r))
    (points (Fin.append (positions l).ofLp (positions r).ofLp)) := by
  unfold realize
  rw [show (fun i => ((points _).ofLp i, Fin.append (tokens l) (tokens r) i)) = Fin.append l.get r.get from ?eq]
  · rw [List.ofFn_fin_append,List.ofFn_get,List.ofFn_get]
  case eq =>
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp <;> rfl

private lemma acrossEq (l r : Cluster F) (x : E4) :
    ∃ n : ℕ, ∃ f : Points n, ∃ p : Fin n → F.W, ∃ i : Fin n, ∀ v : F.W,
      l++ (x,v)::r = realize (update p i v) f := by
  let n := r.length+1
  let i : Fin (l.length+n) := Fin.natAdd l.length (0 : Fin n)
  use l.length+n, points (Fin.append (positions l).ofLp (Fin.cons x (positions r).ofLp)),
    Fin.append (tokens l) (Fin.cons 0 (tokens r)),i
  intro v; rw [clusterEq]
  have hw : @tokens F ((x,v)::r) = Fin.cons v (tokens r) := by
    funext j; refine Fin.cases ?_ (fun _ => ?_) (show Fin n from j) <;> simp <;> rfl
  have hp : (@positions F ((x,v)::r)).ofLp = Fin.cons x (positions r).ofLp := by
    funext j; refine Fin.cases ?_ (fun _ => ?_) (show Fin n from j) <;> simp <;> rfl
  erw [hw,hp]
  congr 1
  funext j; refine Fin.addCases ?_ ?_ j
  · intro k
    erw [Function.update_of_ne (show Fin.castAdd n k ≠ i from fun e => by
      have h := congrArg Fin.val e
      change k.val = l.length+0 at h; omega)]
    simp
  intro k
  refine Fin.cases ?_ ?_ k
  · rw [show Fin.natAdd l.length (0:Fin n)=i from rfl, Function.update_self]
    simp [i,n]
  intro k
  rw [Function.update_of_ne (show Fin.natAdd l.length (Fin.succ k) ≠ i from fun e => by
    have h := congrArg Fin.val e
    change l.length+(k.val+1) = l.length+0 at h; omega)]
  simp

def oneIn (l r : Cluster F) (x : E4) (S : Fields.Kernel F) : F.W →ₗ[ℂ] ℂ where
  toFun v := pointMoment S (l++ (x,v)::r)
  map_add' v w := by
    obtain ⟨n,f,p,i,H⟩ := acrossEq l r x; simp_rw [H,readAt]
    exact MultilinearMap.map_update_add _ _ _ _ _
  map_smul' v w := by
    obtain ⟨n,f,p,i,H⟩ := acrossEq l r x; simp_rw [H,readAt]
    exact MultilinearMap.map_update_smul _ _ _ _ _

-- scale every field in p (retaining parity-order)
def widen (p : Cluster F) (u : ℂ) := p.map fun t => (t.1,u • t.2)
lemma widened {p : Cluster F} (h : Slab a d p) (u : ℂ) : Slab (F:=F) a d (widen p u) := by
  unfold widen
  refine ⟨h.1, ⟨?_,?_⟩, ?_⟩
  · rw [locations,List.map_map]; exact locations.mp h.2.1.1
  · intro k hk; obtain ⟨t,ht,rfl⟩:= List.mem_map.mp hk; exact h.2.1.2 t ht
  intro k hk; obtain ⟨t,ht,rfl⟩:= List.mem_map.mp hk; exact h.2.2 t ht

lemma magnify (S : F.Kernel) (u : ℂ) (l p r : Cluster F) :
    pointMoment S (l ++ (widen p u ++ r)) = u ^ p.length • pointMoment S (l ++ (p ++ r)) := by
  induction p generalizing l with
  | nil => simp [widen]
  | cons z p ih =>
    cases z with
    | mk x v =>
    simp only [widen,List.map_cons,List.cons_append,List.length_cons]
    change oneIn l _ x S (u • v)=_
    rw [map_smul]
    have h1 : ∀ (X w : Cluster F), l ++ ((x,v)::X ++ w)=(l ++ [(x,v)]) ++ (X ++ w) := by intros; simp
    -- l ++ (x :: (X ++ r)) form
    change u • pointMoment S (l ++ ( (x,v)::widen p u ++ r)) = u^(p.length+1) • pointMoment S (l++ ((x,v)::p ++ r))
    rw [h1, ih, h1, smul_smul,pow_succ']

variable (V : Chamber S a)
lemma scaled_plant {p : Cluster F} (hp : Slab a d p) (u : ℂ) (x : Future F a) :
    V.GNS.plant (entering (widened hp u) x)= u ^ p.length • V.GNS.plant (entering hp x) := by
  refine V.GNS.whole.eq_of_inner_right ℂ fun f => ?_
  rw [inner_smul_right]; induction f using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => rw [map_add,inner_add_left,hi,hj,inner_add_left,mul_add]
  | single i c =>
    simp only [YM.Kernel.Gram.stems,Finsupp.linearCombination_single, inner_smul_left,V.GNS.measure]
    unfold kernel; simp only [entering,linked,magnify,smul_eq_mul]; ring

-- use the norm bound on all word sums
lemma gram_norm {n : ℕ} (f : Fin n → Future F a) (c : Fin n → ℂ) :
    ↑(‖∑ i, c i • V.GNS.plant (f i)‖^2) = Fields.gram S a (fun i => (f i).val) c := by
  let w:=∑ i, c i • V.GNS.plant (f i)
  rw [show (↑(‖w‖^2):ℂ) = inner ℂ w w from by rw [inner_self_eq_norm_sq_to_K]; exact Complex.ofReal_pow _ _]
  dsimp only [w]; rw [sum_inner]; simp only [inner_sum, inner_smul_left, inner_smul_right,V.GNS.measure]  
  unfold Fields.gram kernel; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; simp only [Complex.star_def]; ring

variable (E : Fields.Euclidean S)
include E
lemma powered (j D : ℕ) : ∃ (m : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ (d : ℝ≥0) (p : Cluster F), ∀ hp : Slab a d p,
    p.length=j → (∀ x ∈ p, x.2 ∈ F.level D ∧ ‖x.2‖ ≤ 1) → ∀ r : ℝ, 0 < r → r ≤ 1 → buffer a r d p →
    ∃ X : V.GNS.H.Op, ‖X‖ ≤ A * r⁻¹^m ∧ ∀ v : Future F a, X (V.GNS.plant v) = V.GNS.plant (entering hp v) := by
  classical
  obtain ⟨m,A,hA,H⟩:= (E.bounded a).operator j D
  refine ⟨m,A,hA,?_⟩
  intro d p hp he ht r hr h hU
  let M := A*r⁻¹^m
  have hm : 0 ≤ M:=mul_nonneg hA (by positivity)
  apply V.GNS.by_bound _ M hm; intro f
  let z := f.support; let T := Fintype.equivFin z
  let g (i : Fin (Fintype.card z)) : Future F a := (T.symm i).val
  have hb : ‖∑ i, f (g i) • V.GNS.plant (entering hp (g i))‖ ≤ M * ‖∑ i, f (g i) • V.GNS.plant (g i)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hm (norm_nonneg _))).mp
    apply Complex.real_le_real.mp
    rw [mul_pow, Complex.ofReal_mul]
    rw [gram_norm V g (fun i => f (g i)), gram_norm V (fun i => entering hp (g i)) (fun i => f (g i))]
    apply H _ _ hp.1 hr h p he hU ht _ (fun i=> (g i).val) (fun i=> (g i).property)
  have hw (P : Future F a → V.GNS.H) : Finsupp.linearCombination ℂ P f = ∑ i, f (g i) • P (g i) := by
    change ∑ i∈z,f i • P i=_
    rw [←Finset.sum_attach z fun i => f i • P i]
    exact (Equiv.sum_comp T.symm (fun i => f (i:Future F a) • P (i:Future F a))).symm
  simpa only [YM.Kernel.Gram.stems,hw] using! hb

omit V E in
lemma affordable {w : Cluster F} {e : ℝ≥0} (h : Slab a e w) : ∃ r : ℝ, 0<r ∧ r≤1 ∧ buffer a r e w := by
  classical
  have he p (hp : p∈w) : ∀ᶠ r in 𝓝[>] (0:ℝ), r ≤ p.1 a ∧ p.1 a ≤ (e:ℝ)-r := by
    filter_upwards [(gt_mem_nhds (h.2.1.2 p hp)).filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds (sub_pos.mpr (h.2.2 p hp))).filter_mono nhdsWithin_le_nhds] with r hr ht
    exact ⟨hr.le,by linarith [show r<(e:ℝ)-p.1 a from ht]⟩
  have ht i j : ∀ᶠ r in 𝓝[>] (0:ℝ), i ≠ j → r ≤ cubedist (positions w i) (positions w j) := by
    by_cases he : i=j
    · exact Eventually.of_forall fun _ h => (h he).elim
    have hu := h.2.1.1
    have hf : 0<cubedist (positions w i) (positions w j) := dist_pos.mpr
      (fun p => he ((show Injective _ from hu) (WithLp.ofLp_injective _ p)))
    exact ((gt_mem_nhds hf).filter_mono nhdsWithin_le_nhds).mono fun _ hh _ => le_of_lt hh
  have hy := eventually_all_finset _ |>.mpr fun i (hp : i ∈ w.toFinset) => he i (by simpa using hp)
  obtain ⟨r,hr,hp,hH⟩ := ((eventually_all.mpr fun i => eventually_all.mpr (ht i)).and (hy.and (show ∀ᶠ i in 𝓝[>] (0:ℝ), i∈ Ioc 0 1 from Ioc_mem_nhdsGT (by norm_num)))).exists
  exact ⟨r,hH.1,hH.2,hr,by simpa using hp⟩

include V
lemma spread_ready (large : Monotone F.level) (full : ∀ x:F.W, ∃ D,x ∈ F.level D) : Nonempty (Spread V) := by
  classical
  have H (d : ℝ≥0) (w : Cluster F) : ∃ X : V.GNS.H.Op, ∀ hp : Slab a d w, ∀ y : Future F a, X (V.GNS.plant y) = V.GNS.plant (entering hp y) := by
    by_cases h : Slab a d w; swap; exact ⟨0,fun q => (h q).elim⟩
    obtain ⟨R,hR,H⟩ : ∃ R : ℝ, 0<R ∧ ∀ x∈w, ‖x.2‖ ≤ R := by
      have ht := eventually_all_finset _ |>.mpr fun i (_:i∈w.toFinset) => eventually_ge_atTop ‖i.2‖
      simpa using ((eventually_gt_atTop _).and ht).exists
    obtain ⟨D,hD⟩ : ∃ D : ℕ, ∀ x∈w, x.2 ∈ F.level D := by
      have he (x : Plant F) : ∀ᶠ i : ℕ in atTop, x.2∈ F.level i := by obtain ⟨j,hj⟩:=full x.2; exact (eventually_ge_atTop j).mono fun i hi=> large hi hj
      simpa using (eventually_all_finset _ |>.mpr fun i (_:i∈w.toFinset) => he i).exists
    let u:=(↑R:ℂ)⁻¹; have hz : u≠0 := inv_ne_zero (by exact_mod_cast hR.ne')
    have hp (x:Plant F)(hx:x∈widen w u): x.2∈F.level D∧‖x.2‖≤1 := by
      obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
      refine ⟨(F.level D).smul_mem u (hD y hy),?_⟩
      simp only [u,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hR.le]
      exact (inv_mul_le_iff₀ hR).mpr (by linarith [H y hy])
    obtain ⟨r,hr,ht,hm⟩:=affordable (widened h u)
    obtain ⟨m,A,hA,K⟩:=powered V E _ D
    obtain ⟨L,hL,HL⟩:=K d _ (widened h u) rfl hp r hr ht hm
    refine ⟨(u^w.length)⁻¹ • L, fun _ y => ?_⟩; rw [smul_apply,HL y,scaled_plant V h, inv_smul_smul₀ (pow_ne_zero _ hz)]
  choose P HP using H; exact ⟨P,fun hp => HP _ _ hp⟩
omit V E

lemma Spread.rated {V : Chamber S a} (P : Spread V) (E : Fields.Euclidean S) (n D : ℕ) : ∃ (m : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ (d : ℝ≥0) (p : Cluster F), Slab a d p → p.length=n → (∀ x ∈ p, x.2 ∈ F.level D ∧ ‖x.2‖ ≤ 1) → ∀ r : ℝ, 0 < r → r ≤ 1 → buffer a r d p → ‖P.place d p‖ ≤ A * r⁻¹^m := by
  obtain ⟨m,A,hA,H⟩ := powered V E n D
  refine ⟨m,A,hA,?_⟩; intro d p hp he ht r hr h hU
  obtain ⟨X,hX,hW⟩ := H d p hp he ht r hr h hU
  rw [V.GNS.by_bud (M:=V.H.space) (V:=P.place d p) (W:=X) fun i=>(P.reads hp i).trans (hW i).symm]; exact hX
end YM.Massive.Bridge
