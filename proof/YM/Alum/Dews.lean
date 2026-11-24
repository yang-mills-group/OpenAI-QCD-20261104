import YM.Topaz.Room
import YM.Alum.Greet
import YM.Intag.Shift
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Tarot
open Pilgrim Tess Hymnal MassiveQCD.Inky YM.Bloom QCD.Bera Massive.UV YM.Arise YM.Arise.Bill YM.Arise.Count YM.Arise.Range Arise.Parcel
open YM.Eden QCD.Lat Massive.Evo MassiveQCD MassiveQCD.TimesV UV UV.Free QCD.Grass QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Sample Quills Quills.Eden Cupola Ribbon Quills.Clover
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6) {f l:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
variable {l m n:ℕ}(h:p≤ l)(hx:l ≤ m)(hp: Even R.val)
-- l side shadow.S hash check
variable (x:Site (S.side R l))(u:Site (S.side R p))
set_option quotPrecheck false
local notation "Ho"=>evenW S R hp p
include h hx
lemma factorL (hn:m ≤ n): (Column.sky S R p n ((h.trans hx).trans hn) (evenW S R hp p) (Column.pillar S R x m))=(Column.sky S R p n ((h.trans hx).trans hn) (evenW S R hp p) x):=by
      unfold Column.sky Column.pillar; rw [dif_pos hx, dif_pos hn,dif_pos (hx.trans hn)]; rw [embed_comp (viewW S R hx) (viewW S R hn)] -- rw any embed
lemma bitter (k:ℕ)(y:Cover) (hy:wrap _ y∈ (mural (viewW S R h) (evenW S R hp p) x).margin u k): wrap _ (ratioTo S m l • y)∈ (Column.sky S R p m (h.trans hx) (evenW S R hp p) x).margin u (ratioTo S m l*k):=by
      have hZ := stepSpan (viewW S R h) (viewW S R hx) (viewW S R (h.trans hx)) x (wrap _ y) u (evenW S R hp p) (viewOdd S R h) (viewOdd S R hx) k; rw [Ratio.embed_wrap] at hZ; unfold Column.sky Column.pillar; rw [dif_pos hx]; exact hZ.mp hy
lemma tender (U k:ℕ)(hu:0<U)(hv:marginM S U p l+ 1 ≤ k) : marginM S U p m ≤ ratioTo S m l * k:=by
     let a:= ratioTo S l p; let b:=ratioTo S m l
     unfold marginM at hv ⊢; rw [show ratioTo S m p=b*a from size_comp (viewW S 1 h) (viewW S 1 hx) (viewW S 1 (h.trans hx))];
     have he:a< k*U:= (Nat.div_lt_iff_lt_mul hu).1 hv
     have hx:0< b:=(odd_to hx).pos
     exact ((Nat.div_lt_iff_lt_mul hu).2 ((Nat.mul_lt_mul_of_pos_left he hx).trans_eq (mul_assoc ..|>.symm) : b*a< b*k*U)).le
open CardsT
variable (U:ℕ)(hu:0<U)(t:Cover)(K:ℕ)
include hu
lemma budding (s:Cover)(hv:s∈ box (CardsT.flex S l m))(hxT:wrap _ t∈(mural (viewW S R h) (evenW S R hp p) x).margin u (marginM S U p l+102+K)):wrap (S.side R m) (ratioTo S m l • t +s)∈ (Column.sky S R p m (h.trans hx) (evenW S R hp p) x).margin u (marginM S U p m+(ratioTo S m l)*K):=by
       have hw:= bitter h hx hp x u _ t hxT; let A:=ratioTo S m l; have ht:marginM S U p m ≤ A*(marginM S U p l+1):= tender h hx U _ hu le_rfl
       have hB : 0<A := (odd_to hx).pos
       let B:=marginM S U p l; let q:=marginM S U p m+A*K; have hβ:CardsT.flex S l m+1+q ≤ A*(B+102+K):=by unfold CardsT.flex q; change 100*(A-1) + _ +_ ≤ _; rw [mul_add,mul_add]; change _ ≤ A*B+_*_+_; change marginM S U p m ≤ A*(B+1) at ht; rw [mul_add,mul_one] at ht; omega
       rw [map_add,add_comm _ (wrap (S.side R m) s)]; refine marginB _ (padding (viewW S R (h.trans hx)) _ _ _ _ (show Odd (ratioTo S m p) from odd_to (h.trans hx)) hw (show CardsT.flex S l m + 1 + (marginM S U p m+(ratioTo S m l)*K) ≤ _ from hβ)) ?_; obtain ⟨hx,hz⟩:= box_test.mp hv; intro j; specialize hx j; specialize hz j; omega
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.factorL
#print axioms YM.Intag.Tarot.Vista.budding
