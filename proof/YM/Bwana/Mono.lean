import YM.Bwana.View
import YM.Pods.Typing
import YM.Push.FREE_RESOLVENT.Torus
/-! universal cover supplying literal displacements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth.Off
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Plans Display Orientation Exposure Rolls Canvas
variable {S:Scheme}{r:Side}{N J d i j m k:ℕ}(A:Run S N r 6)
open Planned.PrimaryIntegral295 Carrier Laurent Hub Next.Rank.Station
noncomputable def lineC (S:Scheme)(b:ℕ→ Cover)(t:ℕ)(x:Cover)(i:ℕ):= b i+ ratioTo S i t • x
local notation "Pℓ"=> lineC S
lemma ruler (h:i≤ j)(hh:j ≤ k): ratioTo S k i=ratioTo S k j* ratioTo S j i:= size_comp (viewW S 1 h) (viewW S 1 hh) (viewW S 1 (h.trans hh))
lemma rink(h:i ≤ j) : ratioTo S (j+1) i=(S.step j).L.val * ratioTo S j i:= size_comp (viewW S 1 h) (stitch S 1 j).ratio (viewW S 1 (Nat.le_step h))
variable (b:ℕ→ Cover)(hB:Borders S j N b)(x:Cover)
include hB
lemma drafted(h:j ≤ m): Borders S m N (lineC S b m x):=by intro i he hi; unfold lineC; rw [rink he, mul_smul, offsetC,hB _ (h.trans he) hi]
omit hB
lemma ledger (h:m≤ i)(hh:i≤ N): lup S b N i (lineC S b m x i)=lineC S b m x N:=by unfold lup lineC; rw [add_sub_cancel_left,ruler h hh,mul_smul]
variable (R:Side)
lemma parish : ∀ V:Ratio r R,V.count.val=1→ ∀ a: Cover,V.parent (wrap R a)= wrap r a:=by
      intro V h a; rw[Streets.owner]; apply congr_arg; -- cellar identity when L=1
      have hB:=balance V.count a; have hx : ∀ L:Side,L=1→cellar L a=a := by
           intro L h; subst L; have hb:=balance 1 a; change a=lift (wrap 1 a)+(1:ℕ) • cellar 1 a at hb; rw[one_smul,show wrap 1 a=0 from (by ext i; change ((a i:ℤ):ZMod 1)=0; exact Subsingleton.elim _ _),show lift (0:Site 1)=0 from (by ext;simp [lift];rfl),zero_add] at hb; exact hb.symm
      exact hx _ (Subtype.ext h)
include hB
lemma patron (hN:i ≤ N)(hj:j ≤ i): (viewW S R hN).parent (wrap (S.side R N) (b N))= wrap (S.side R i) (b i):=by
      induction hN using Nat.decreasingInduction with
      | self=> exact parish (S.side R N) (viewW S R (k:=N) (n:=N) le_rfl) centreN _
      | of_succ i h ih=>
          have hh:= ih (hj.trans (Nat.le_succ i)); rw [parent_nested (stitch S R i).ratio (viewW S R h) (viewW S R h.le) (S.step i).odd (odd_to (S:=S) h), hh,Streets.owner]; exact congr_arg _ (hB _ hj h)
-- independence from periods by testing arbitrarily large
omit hB
noncomputable abbrev meanC (S:Scheme){N:ℕ}{i:ℕ}(h:i ≤ N): Side:= ⟨ratioTo S N i,(odd_to h).pos⟩
-- produce `b_i` for given cutoff x.
noncomputable def faceC (S:Scheme)(N:ℕ)(x:Cover)(i:ℕ): Cover:= if h:i=N then x else if h:i < N then cellar (meanC S h.le) x else 0
local notation "φ"=>faceC S N x
lemma face_seat (h:i≤ N) :∀ R:Side, wrap (S.side R i) (φ i)=(viewW S R h).parent (wrap (S.side R N) x):=by
      intro R; unfold faceC; split
      next h=> subst i; exact (parish (S.side R N) (viewW S R (k:=N) (n:=N) le_rfl) centreN _).symm -- binder R here
      next hh=> rw[dif_pos (lt_of_le_of_ne h hh),Streets.owner]; -- rfl
lemma wrap_lives {x y:Cover} (h:∀ R:Side,wrap (S.side R i) x=wrap (S.side R i) y): x=y:=by
      let m:=max (size x) (size y); let B:Side:=⟨2*m+1,Nat.succ_pos _⟩; have hh :2*m < (S.side B i).val:= by rw[Scheme.side, PNat.mul_coe]; exact lt_of_lt_of_le (by unfold B; dsimp; omega) (Nat.le_mul_of_pos_right B.val (S.ratio i).property)
      exact (FreeResolvent.size_centers _ x (le_max_left ..) hh).symm.trans ((congr_arg lift (h B)).trans (FreeResolvent.size_centers _ y (le_max_right ..) hh))
lemma face_b : Borders S j N (faceC S N x):=by
      intro i _ hi; apply wrap_lives (S:=S) (i:=i); intro R
      let L:= (stitch S R i).ratio; rw[show (S.step i).L=L.count from rfl,← Streets.owner L, face_seat x hi,face_seat x hi.le]; exact (parent_nested L (viewW S R hi) (viewW S R hi.le) (S.step i).odd (odd_to (S:=S) hi) _).symm
lemma head_face :faceC S N x N=x:=by unfold faceC; simp -- if hw unused lean still dite
lemma perch(h:i ≤ N) (hv:2*size x< ratioTo S N i): (faceC S N x) i=0:=by
      let Y:= meanC S h
      apply wrap_lives (S:=S) (i:=i); intro R; rw[face_seat x h,Streets.owner]; apply congr_arg; change cellar Y x=0; have hh:=balance Y x; rw[FreeResolvent.size_centers Y x le_rfl hv] at hh; apply smul_right_injective Cover Y.pos.ne'; dsimp only; rw [smul_zero]; exact add_left_cancel ((add_zero x).trans hh).symm
lemma lead_face (hj:j≤ i)(h:i ≤ N)(hp:2*size x<ratioTo S N i): faceC S N x j=0:=by apply perch x (hj.trans h); rw [ruler hj h]; exact hp.trans_le (le_mul_of_one_le_right (Nat.zero_le _) (odd_to (S:=S) hj).pos)
end YM.Massive.Patria.Depth.Off
#print axioms YM.Massive.Patria.Depth.Off.drafted
#print axioms YM.Massive.Patria.Depth.Off.ledger
#print axioms YM.Massive.Patria.Depth.Off.patron
#print axioms YM.Massive.Patria.Depth.Off.face_b
#print axioms YM.Massive.Patria.Depth.Off.head_face
#print axioms YM.Massive.Patria.Depth.Off.lead_face
