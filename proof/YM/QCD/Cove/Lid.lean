import YM.QCD.Cove.Port
/-! # build a word. Large uses only wall when roots active. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{t:ℝ}{f c: Side}{S: Ratio c f}
variable {E J D: Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F

abbrev Fj (D E J:Type):= D ⊕ (E ⊕ J)
namespace Fj
variable (s w:Finset (Fj D E J))
def ops := s.toLeft
def leftE := s.toRight.toLeft
def spent := s.toRight.toRight
def pin (O:Finset D)(X:Finset E)(K:Finset J) : Finset (Fj D E J):=O.disjSum (X.disjSum K)
lemma pinch : pin (ops s) (leftE s) (spent s)=s:=by ext k; rcases k with k|k|k <;> simp [ops,leftE,pin,spent]
@[simp] lemma pinC (O: Finset D)(X:Finset E) (K : Finset J): ops (pin O X K)=O:=by simp [pin,ops]
@[simp] lemma pinX (O: Finset D)(X:Finset E) (K : Finset J): leftE (pin O X K)=X:=by simp [pin,leftE]
@[simp] lemma pinK (O: Finset D)(X:Finset E) (K : Finset J): spent (pin O X K)=K:=by simp [pin,spent]

def each (D E J : Type): Finset D × (Finset E × Finset J) ≃ Finset (Fj D E J) where
 toFun z:= pin z.1 z.2.1 z.2.2
 invFun x:=(ops x,leftE x,spent x)
 left_inv x:= by simp
 right_inv := pinch
end Fj
open Fj
variable (g:Send S F D) (P:Rise f F E J)(t:ℝ)
variable {s w: Finset (Fj D E J)} 

def native (i:Fj D E J):Support f:=Sum.elim g.rooms (Sum.elim (fun i=> (P.row i).support) (fun i=> (P.front i).place)) i
def coreW (s:Finset (Fj D E J)):= s.biUnion (native g P)
def bucks (i:D)(U:Grid f): EndA (Junta c f F):=excess (g.treats i U)

def made (U:Grid f)(s : Finset (Fj D E J)): EvenA f F:=(∏ i∈leftE s,(NormedSpace.exp (P.reading t U i)-1)) *∏ j∈ spent s,P.plug j U -- g not binder

def axle (U:Grid f)(s: Finset (Fj D E J)): EndA R:=
    (ops s).noncommProd (fun i=> bucks g i U) (by intro i _ j _ _; exact ((Commute.symm (roundP (roundP (g.hat U j i).symm).symm)).sub_left (by exact Commute.one_left _)).sub_right (Commute.one_right _))
lemma forces (U:Grid f)(s:Finset (Fj D E J)): Stays (axle g U s) (hooks S (coreW g P s)) := by
  refine noncommProd_induction (ops s) (fun i=> bucks g i U) (by intro i _ j _ _; exact ((Commute.symm (roundP (roundP (g.hat U j i).symm).symm)).sub_left (by exact Commute.one_left _)).sub_right (Commute.one_right _)) (fun x=> Stays x (hooks S (coreW g P s))) ?_ ?_ ?_
  · intro a b ha hb; exact ha.paysM hb
  · apply Stays.paidI
  intro i hi; apply (g.weld U i).heel; intro q h; rw [hooked] at *; exact mem_biUnion.mpr ⟨Sum.inl i,by simpa [ops] using hi, h⟩ -- check

def crate (s: Finset (Fj D E J)) (U: Grid f) : Patio R:=⟨axle g U s (near A B (light _ (made P t U s))), (forces g P U s).evenPay (bright (ahead S F (made P t U s))) ⟩
def dye (s:Finset (Fj D E J)) (U:Grid f): EvenA c F:= accord S F (g.shortP U) (crate g P t s U)
lemma dipping (s: Finset (Fj D E J)) (U: Grid f) : light _ (dye g P t s U) = wipe A B (g.shortP U) (axle g U s (near A B (light _ (made P t U s)))):=rfl

lemma limitsMon (X Y: Support f)(h:X⊆Y): limits (F:=F) X⊆ limits Y:=fun i hi=> mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hi).2⟩
lemma gateMon (X Y: Support f)(h:X⊆Y)(x:EvenA f F)(hh:Gated X x): Gated Y x:= regionMon (limitsMon X Y h) hh -- syntax
lemma gate_exp (X:Support f)(x: EvenA f F)(h:Gated X x) : Gated X (NormedSpace.exp x -1):=by
  unfold Gated; rw [map_sub,map_one,light_exp]
  let z := light _ x; apply Subalgebra.sub_mem _ _ (Subalgebra.one_mem _); apply Stays.tab _ (exp_series_hasSum_exp' (𝕂:=ℂ) z); exact fun i=> Subalgebra.smul_mem _ (Subalgebra.pow_mem _ h _) _
lemma gate_prod {I:Type*} (Q :I→EvenA f F)(X:Support f)(s:Finset I)(h:∀ i∈s,Gated X (Q i)): Gated X (∏ i∈s,Q i) := by
  induction s using Finset.induction_on with
  | empty=> unfold Gated; rw [prod_empty,map_one]; exact Subalgebra.one_mem _
  | insert i s hi ih=> unfold Gated; rw [prod_insert hi,map_mul]; exact Subalgebra.mul_mem _ (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma wears (s:Finset (Fj D E J)) (U:Grid f)(h:P.Wave t): Gated (coreW g P s) (made P t U s):=by
  unfold Gated made; rw [map_mul]
  apply Subalgebra.mul_mem
  · apply gate_prod; intro i hi; apply gateMon _ _ _ _ (gate_exp _ _ (P.readable t h i U)); intro m hm; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inl i),by simpa [leftE] using hi, hm⟩
  apply gate_prod; intro i hi; apply gateMon _ _ _ _ (h.chair i U); intro m hm; exact mem_biUnion.mpr ⟨Sum.inr (.inr i), by simpa [spent] using hi,hm⟩
lemma framed (s:Finset (Fj D E J))(U:Grid f)(h:P.Wave t): light _ (crate g P t s U)∈region (hooks S (coreW g P s)):=by
  refine (forces g P U s).keeps (Subset.refl _) _ (effects _ ?_ _ (wears g P t s U h))
  intro i hi; change near A B (atom i)∈_; change embed (ha c f F) (atom i)∈_; rw [embed_atom]; apply marked; rw [hooked,rootA]; exact (mem_filter.mp hi).2
lemma halo_dye (s:Finset (Fj D E J))(U:Grid f)(h:P.Wave t)(Z:Support c)(he : (halo g.trim (coreW g P s)).image S.parent ⊆ Z): Gated Z (dye g P t s U):=by
  refine effects (wipe A B (g.shortP U)) ?_ _ (framed g P t s U h); intro i hi; rcases splits_index i with ⟨v,rfl⟩|⟨v,rfl⟩
  · change ha _ _ _ v∈_ at hi; rw [hooked,rootA] at hi
    rw [wiper]; apply Subalgebra.sum_mem; intro j _; by_cases hx:g.shortP U v j=0
    · rw [hx,zero_smul]; exact Subalgebra.zero_mem _
    apply Subalgebra.smul_mem; apply marked; apply mem_filter.mpr; refine ⟨mem_univ _,he ?_⟩
    have hy:=g.sleeps v j U hx; exact mem_image.mpr ⟨_, (Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi) hy), S.embed_parent _⟩ -- name
  · change hb _ _ _ v∈_ at hi; rw [hooked,rootB] at hi
    rw [tails]; apply marked; apply mem_filter.mpr; exact ⟨mem_univ _,he (mem_image.mpr ⟨S.embed _,halo_subset _ _ hi,S.embed_parent _⟩)⟩
end YM.QCD.Cove
