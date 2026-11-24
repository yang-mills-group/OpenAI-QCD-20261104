import YM.Intag.Yell
import YM.Intag.Crown
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
open Sample Quills Quills.Eden Cupola Ribbon
open Massive.Elm.SparK.Arbor Massive.Elm.SparK.Arbor.Gallery
open QCD.Plum QCD.RP QCD.Cove QCD.Creek QCD.Bloom Metric Laurent Precision Bloch Exterior
open Column Massive.Evo
variable {S:Scheme}{R:Side}{i j k p N:ℕ}(A: Massive.Run S N R 6) {f l:Side}{D:ℕ}
namespace Vista
open YM.Bloom.Jar YM.Bank YM.Bank.Jule
variable {I:Type}[Fintype I](x:I→ Cover)(b:ℕ) (Tq:ℝ)(ε v:ℝ)
variable (ht:0<Tq)(h:∀ i j:I,i≠j→ posT Tq b (x i) -posT Tq b (x j) ∈ Oasis ε v)
variable (hv:p ≤ i)(w:Site (S.side R i))(ho:Even R.val)(P:Site (S.side R p))(L:List I)
local notation "Hp"=> evenW S R ho p
local notation "G"=> viewW S R hv
set_option quotPrecheck false
variable (U M X t:ℕ)
noncomputable def marginM (S:Scheme) (U p i:ℕ) := ratioTo S i p/U
variable (hs:0<U)(hj:p ≤ j)(hJ:j ≤ i) (hP:U*(X+M*M+1) ≤ ratioTo S j p)
include hs hj hJ hP
lemma compass : X ≤ marginM S U p i ∧ ratioTo S i j*(M*M+1) ≤2*marginM S U p i:=by
    let L:=ratioTo S i j; let Q:=ratioTo S j p; let s:=L*(X+M*M+1)
    have hv:s*U ≤ ratioTo S i p:=by
         rw [show ratioTo S i p=L*Q from YM.Next.Rank.Station.size_comp (viewW S 1 hj) (viewW S 1 hJ) (viewW S 1 (hj.trans hJ))]; unfold s; rw [mul_assoc,mul_comm (X+M*M+1) U]; exact Nat.mul_le_mul_left _ hP
    have hm:s ≤ marginM S U p i:= (Nat.le_div_iff_mul_le hs).mpr hv
    have he : X ≤ s:= (show X ≤ X+M*M+1 from (by omega)).trans (le_mul_of_one_le_left (Nat.zero_le _) ((odd_to hJ).pos:1 ≤ L))
    exact ⟨he.trans hm, (Nat.mul_le_mul_left L (show M*M+1 ≤ X+M*M+1 from by omega)).trans (hm.trans (le_mul_of_one_le_left (Nat.zero_le _) (by omega)))⟩
include h ht
lemma canopy (hz:L.Nodup)(hK:∀ i,i∈L)(hk:Fintype.card I ≤ t)(hc:0<ε)(hx:2*(v*Tq^b)<((S.side R i).val:ℝ))(hY: v*Tq^b≤ (ratioTo S i j:ℝ))(hZ:(4:ℝ)*X< ε*Tq^b)(hO:∀ t,wrap (S.side R i) (x t)∈(mural G Hp w).margin P (marginM S U p i)): Reception hv ho w P x L X M (marginM S U p i) t j b Tq ε v:=by
        have H (u z:I)(h':u≠z):=Consent.rootV (x u) (x z) Tq b ht ε v (h u z h') hx
        obtain ⟨hm,hvM⟩:= compass (S:=S) U M X hs hj hJ hP
        refine ⟨⟨hz,hK⟩,hk,hc,hO,hm,hvM,fun u v=>?_,?_,h⟩
        · by_cases h':u=v; · subst u; simp
          exact_mod_cast ((H u v h').2.trans hY)
        intro u v h'; have h_ := lt_of_lt_of_le hZ ((H u v h').1); exact_mod_cast (lt_of_mul_lt_mul_left (show 2*((2:ℝ)*X) < 2* (separation (wrap (S.side R i) (x u)) (wrap _ (x v)):ℝ) by linarith only [h_]) (by norm_num:(0:ℝ) ≤ 2))
omit h ht
lemma pegR (x:Cover)(hs':1≤ t)(hc:0<ε)(hy:wrap (S.side R i) x ∈ (mural (viewW S R hv) Hp w).margin P (marginM S U p i)): Vista.Reception hv ho w P (fun _:Unit=>x) [()] X M (marginM S U p i) t j b Tq ε v:=by obtain ⟨h1,h2⟩:= compass (S:=S) U M X hs hj hJ hP; exact ⟨⟨by simp,by simp⟩,by simpa using hs',hc,fun _=> hy,h1,h2,fun _ _ => by simp,fun _ _ h=>False.elim (h (Subsingleton.elim ..)),fun i j h=>False.elim (h (Subsingleton.elim ..))⟩
end Vista
end Tarot
end YM.Intag
#print axioms YM.Intag.Tarot.Vista.canopy
#print axioms YM.Intag.Tarot.Vista.pegR
