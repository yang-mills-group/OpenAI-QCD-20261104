import YM.Pods.Gleams
import YM.Cells.Proximity

/-!
# Arbitrary positions of all the localized continuous parity-homogeneous
invariant test fields, all possible aspect tilings along the path
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Romance
open QCD QCD.Lat QCD.RP QCD.Grass Lattice Wilson MeasureTheory Function Filter Finset NormedSpace
open Chess Cells Tiling Chess.Fortuna
open scoped BigOperators Topology Matrix.Norms.L2Operator ComplexOrder Classical
variable {A : Type*} {n : Side} {F : ℕ} {x y : Insertion n F}
variable {p k r m:ℕ} (T : Tiling n) (V : Insertion n F→ₗ[ℂ]ℂ)(R: Regulator n F) {J:RG.Patch}{e:ℝ}
variable (hp : T.kind=.link)

section placement

/- Sparse ordered list of *fields localized* at distinct cells,
no permutation invariance presumed, can be inserted in any requested order. -/
variable [Fintype A] (x:A→Insertion n F) (c:A→T.Cell)
include hp
lemma plant (hc : Injective c)(v:ℕ)(L:List A)(hr:L.Nodup)(hk:∀ i,i∈L)(hx:∀ i,Base T (c i) v (x i))(hR:R.t=0)(he:Chess.Fortuna.Seal V R T v)(hv:V 1=1): ‖V (L.map x).prod‖ ≤ ∏ i:A, floorL T V R (x i) (c i):=by
   let f (i:T.Cell):Insertion n F:= if h:∃ j,c j=i then x (Classical.choose h) else 1
   have hf(i): f (c i)= x i:=by unfold f; rw [dif_pos ⟨i,rfl⟩]; exact congr_arg x (hc (Classical.choose_spec (show ∃ j,c j=c i from ⟨i,rfl⟩)))
   let s:=univ.image c
   have h(i:T.Cell)(ht:i∉s): f i=1:= dif_neg (fun ⟨j,hj⟩=> ht (mem_image.mpr ⟨_,mem_univ j,hj⟩))
   have hP(i:T.Cell): Base T i v (f i):=by
       by_cases ht:i∈s
       · obtain ⟨j,-,rfl⟩:=mem_image.mp ht; rw [hf]; exact hx j
       rw [h i ht]; exact ⟨flooring_one,invariant_one,false, fun i=> by simp [Hom, Plus]⟩
   let C:=(sᶜ).toList;
   have h1:List.Perm ((L.map c) ++ C) (univ:Finset T.Cell).toList:=by -- syntax replace
       refine (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨hr.map hc,nodup_toList _,?_⟩) (nodup_toList _)).2 ?_
       · intro i hi j hj he; subst j; obtain ⟨j,-,rfl⟩:= List.mem_map.mp hi; have hu:=mem_compl.mp (mem_toList.mp hj); exact hu (mem_image.mpr ⟨j,mem_univ j,rfl⟩)
       intro i; by_cases hz:i∈s
       · obtain ⟨j,-,rfl⟩:= mem_image.mp hz; exact iff_of_true (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨j,hk j,rfl⟩))) (by simp)
       exact iff_of_true (List.mem_append.mpr (.inr (mem_toList.mpr (mem_compl.mpr hz)))) (by simp)
   let B (i:T.Cell)(j:T.Cell):= replicateR T R (f i) i j
   have h₂ (l:List T.Cell): Chess.Array.use T l B id=(l.map f).prod:= by
       unfold Chess.Array.use; congr 2; funext i; exact moved_at ..
   have h₃ : (C.map f).prod=1:=List.prod_eq_one (by rintro i hi; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hi; exact h v (mem_compl.mp (mem_toList.mp hv))) -- name?
   have h₄: Chess.SignedEq (L.map x).prod (tally T f):= by
       have hL:= Array.rearrange id (K:=B) ((figure T R hp id f hP hR).toPattern) _ _ h1; rw [h₂,h₂,List.map_append,List.prod_append,List.map_map, h₃,mul_one,(show f∘c=x from funext hf)] at hL; exact hL --  namespace
   rw [Chess.Fortuna.Array.holds_period V h₄]; apply (many T V R hp f hP hR he).trans_eq; rw [← Finset.prod_subset (Finset.subset_univ s)]; change (∏ i∈univ.image c,floorL T V R (f i) i)=_; rw [Finset.prod_image hc.injOn]; simp_rw [hf]
   intro i hi he; rw [h i he, roof_blank T V R i hv] -- replace
omit hp

end placement

abbrev Window (x:Site n)(r:ℕ) : Set (Site n):= (fun v:Cover=> wrap n v+x) '' (box r:Set Cover)

lemma marginB {x : Site n} {v : T.Cell} {k b} (hx : x∈T.margin v (k+b)) {z : Cover}
    (hz : ∀ a, (z a).natAbs < k) : wrap n z+x ∈ T.margin v b := by
  have he:= T.fits_stencil hx (fun i=> ((hz i).trans_le (by omega) : (z i).natAbs < k+b))
  refine ⟨he,fun i => ?_⟩
  have he := hz i
  obtain ⟨hr,h⟩ := (show _∧_ from hx.2 i)
  let a := T.coordinated v x i
  let w : ℤ := ↑a + z i
  change k+b ≤ a at hr; change a+_+_ ≤ _ at h
  have ht' : 0 < w := by dsimp [w];omega
  have ht : w.toNat < T.side.val := by dsimp [w]; omega
  have hs : T.coordinated v (wrap n z+x) i = w.toNat := by
    unfold coordinated
    rw [show (wrap n z+x) i-T.starts v i = ((w.toNat:ℕ):Per n) from ?_, ZMod.val_natCast_of_lt (ht.trans T.narrow)]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg ht'.le]; unfold w a; push_cast
    change (z i:Per n)+x i-T.starts v i=_
    simp [coordinated, Per]; abel
  rw [hs]; unfold w; omega

/-- Cloud of **any** fields which fit in these cubes (incl when locally Marked
and translated, not tied to any one preferred center of the tiling). Reference point may be
close to the cut or AP-sign conductor. Fixed integer stencil at its reading rung. -/
structure Within (x: Site n)(a:ℕ)(y:Insertion n F) :Prop where
    floor : Floors (Window x a) y
    good : Lat.Invariant y
    parity : Chess.Parity y
def Clear (w : ℕ)(x: Fin m→ Site n) := ∀ i j, i≠j → w < separation (x i) (x j)

lemma placement (x: Fin m→ Site n) (h:Clear T.side.val x)(hr : m*(2*(r+1+k)) < T.side.val) : ∃ o : Site n, let B := T.newly o; let c := fun i=> B.which (x i); Injective c ∧ ∀ i, Window (x i) r ⊆ B.margin (c i) k := by
   obtain ⟨o,ho⟩:= fits_together T x (r+1+k) (by omega) hr
   refine ⟨o,?_⟩; intro B c; constructor
   · intro i j h'; by_contra he; exact ((not_le.mpr (show B.side.val< _ from h i j he)) (B.extent (v:=c j) (h' ▸ (ho i).1) (ho j).1))
   rintro i x ⟨z,h,rfl⟩; obtain ⟨h1,h2⟩:= box_test.mp h; apply marginB _ (ho i); intro v; specialize h1 v; specialize h2 v; omega

end YM.Massive.Romance
#print axioms YM.Massive.Romance.plant
