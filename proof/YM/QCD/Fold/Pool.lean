import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Squirms
import YM.QCD.Fork.Ridge

/-! # Economical **exact** reprint of cylindrical short letters. Winding pieces
move to long. No logarithmic loss even for sparse disconnected supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Fork Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame
open scoped Classical
variable {c C f F:Side} (h:f.val ∣ F.val){D B b:ℕ}
local notation "π"=> (Macrame.splitter h)
lemma tendle (x i:Site f): i∈trunkFt x B ↔ separation x i≤B:=by simp [trunkFt,halo_spec]
lemma pulse {X:Support F} {x i:Site F}(h:ReflTransGen (Corona.Touch X 1) x i)(hp:B<separation x i):∃ p∈X,separation x p=B+1 :=by
  induction h with
  | refl=> simp at hp -- Nat
  | @tail i j _ hr ih=>
    by_cases ht:B < separation x i
    · exact ih ht
    obtain ⟨h1,h2,h3⟩:=hr; exact ⟨j,h2,Nat.le_antisymm ((separation_triangle x i j).trans (Nat.add_le_add (le_of_not_gt ht) h3)) hp⟩
-- map drum
lemma parked (D:Support F)(X:Support F)(hp:covers b X D): covers b (X.image π) (D.image π):=by
   obtain ⟨k,hk⟩:= (show f.val ∣ F.val from h); have hv: halo b (D.image π) = (halo b D).image π:= ringed hk D b
   have hd: ∀ x∈halo b D,∀ y∈ halo b D,ReflTransGen (Corona.Touch (halo b D) 1) x y:=hp.2
   refine ⟨hv.symm ▸ image_mono π hp.1,?_⟩
   intro x hx y hy; change ReflTransGen (Corona.Touch _ 1) x y
   rw [hv] at hx hy; obtain ⟨x,hx',rfl⟩:= mem_image.mp hx; obtain ⟨y,hy',rfl⟩:=mem_image.mp hy
   rw [hv]; clear hx hy; induction hd x (by assumption) y (by assumption) with
   | refl=> exact .refl
   | @tail i j _ hp ih => exact (ih hp.1).tail ⟨mem_image_of_mem _ hp.1,mem_image_of_mem _ hp.2.1,(less h ..).trans hp.2.2⟩

lemma lilac (X: Support F)(b:ℕ): coverNumber b (X.image π) ≤ coverNumber b X:=by
   obtain ⟨x,hx,hX⟩:= coverNumber_realized b X; exact (Corona.list_cost _ (parked h _ _ hx)).trans (card_image_le.trans_eq hX)
lemma kettle (x y:Site F)(hp:x∈trunkFt y B)(ht:4*B<f.val){X:Support F}(hv:X ⊆ trunkFt y B) : X⊆trunkFt x B ↔ X.image π ⊆ trunkFt (π x) B:=by
   constructor
   · intro ht _ hi; obtain ⟨i,hi',rfl⟩:= mem_image.mp hi; exact (tendle ..).2 ((less h ..).trans ((tendle ..).1 (ht (by assumption))))
   intro hT i hi; apply (tendle ..).2; have he : 2*separation x i < f.val:=by
     have he:= separation_triangle x y i; rw [separation_comm x y] at he; have hy:=(tendle ..).1 hp; have hk := (tendle ..).1 (hv hi); omega
   rw [teaches h x i he]; exact (tendle ..).1 (hT (mem_image_of_mem π hi))

structure Seems (x y:Site F) (X:Support F)(b B:ℕ)(V:Support f):Prop where
  offers : X.image π⊆ V
  cheap : coverNumber b V≤ coverNumber b X
  site : x∈X → y ∈ X → ∀ z∈({x,y}:Finset _), X⊆trunkFt z B ↔ V⊆trunkFt (π z) B
lemma kinds (x:Site F){X D:Support F}(he: covers b X D) (hx:x ∈X) (ht:2*(B+1)<f.val)(hy: (halo b D).image π ⊆ trunkFt (π x) B) : X ⊆trunkFt x B:=by
   intro i hi; apply (tendle ..).2; by_contra! hq; obtain ⟨z,hz,H⟩:= pulse (X:=halo b D) (he.2 _ (he.1 hx) _ (he.1 hi)) hq
   have he:=(tendle ..).1 (hy (mem_image_of_mem π hz)); rw [← teaches h x z (by omega)] at he; omega
lemma pillows (x y:Site F)(X:Support F)(ht:4*B+3<f.val)(b:ℕ):∃ V,Seems h x y X b B V:=by
   by_cases he:x∈X ∧ y ∈X; swap; exact ⟨_,⟨Subset.rfl,lilac h X b,fun u v=>(he ⟨u,v⟩).elim⟩⟩
   have hc : ({x,y}:Support F)⊆X:= by intro i hi; simp only [mem_insert,mem_singleton] at hi; rcases hi with rfl|rfl; exact he.1; exact he.2
   by_cases hx : ∃ z∈({x,y}:Support F), X⊆trunkFt z B
   · obtain ⟨z,hz,H⟩:=hx; exact ⟨_,⟨Subset.rfl,lilac h X b,fun _ _ j hj=> kettle h j z (H (hc hj)) (by omega) H⟩⟩
   obtain ⟨V,hV,hX⟩:= coverNumber_realized b X
   refine ⟨(halo b V).image π,⟨image_mono π hV.1,(Corona.list_cost _ (parked h V _ (show covers b (halo b V) V from ⟨Subset.rfl,hV.2⟩))).trans (card_image_le.trans_eq hX),fun _ _ p hp=>?_⟩⟩
   exact ⟨fun H=>(hx ⟨p,hp,H⟩).elim,kinds h p hV (hc hp) (by omega)⟩

def pool (x y : Site F)(X: Support F)(b B:ℕ): Finset (Support f) := univ.filter (Seems h x y X b B)
def loan (x y:Site F)(X:Support F)(b B:ℕ)(V:Support f):ℝ:= let A:=pool h x y X b B; if V ∈A then (A.card:ℝ)⁻¹ else 0
lemma cushion (x y : Site F)(X:Support F)(b B:ℕ) (V:Support f):0≤ loan h x y X b B V:=by simp only [loan]; split_ifs<;>positivity
lemma purse (x y:Site F)(X:Support F)(b B:ℕ)(hv:4*B+3<f.val): ∑ V,loan h x y X b B V=1:=by
   let A:= pool h x y X b B; change ∑ V,ite (V∈A) _ _=1; classical
   rw [← sum_filter,sum_const,nsmul_eq_mul]; have hS:univ.filter (fun V=> V∈A)=A:= Finset.ext fun i=> by simp
   obtain ⟨i,hi⟩:= pillows h x y X hv b; have hT:0<(A.card:ℝ):= Nat.cast_pos.mpr (card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩); rw [hS,mul_inv_cancel₀ hT.ne']
lemma glimpse (x y:Site F)(X:Support F)(b B:ℕ)(V:Support f)(hp:loan h x y X b B V ≠0): Seems h x y X b B V:= (mem_filter.mp (show V∈pool h x y X b B from by by_contra he; unfold loan at hp; simp only [he,ite_false,ne_eq,not_true_eq_false] at hp)).2
end YM.QCD.Folding
