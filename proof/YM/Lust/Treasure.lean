import YM.ValeK.San
import YM.ValeK.Toxic
import YM.Topaz.Jubilee
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Vale
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
open RG
open Poised Poised.Plans Poised.Plans.Stamp
variable {Vb:YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb) (Θ: Massive.SourceRead.TaperHol)(sym:RawSym)(Y: Massive.Sequence)(U:Lining.Temper.Collage.Exhibit.CoreMix)
variable {S:Scheme}{R:Side}{i p j N:ℕ}(A: Massive.Run S N R 6)
open Lattice Wilson Cells YM.Next.Rank.Station Ibis
open Tarot Tarot.Vista Pilgrim Tess Hymnal
open MassiveQCD
open QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open QCD.Acre.Stratum.MarchQ.Suburb.Sapphire QCD.Acre.Stratum.MarchQ.Suburb.MintV Metric
variable {d D:ℕ}
variable (H:∀ d,Laurel d)(J:∀ d,Landing sym (H d))
local notation "IX"=> Fin (D+1)
variable (L:Side)
set_option quotPrecheck false
-- board commitment for all finite calls in regulators geometry.Supportsystem.
include J
lemma dawnT (Hp:Dial D)(e v:ℝ)(u K:ℕ)(hu:100*(K+1)≤u)(hV:11<Hp.R)(hHp:Hp.R<Hp.e)(hE:0<e)(hv:0<v)(hL:1 < L.val):∀ᶠ z in atTop,(∀ i:ℕ,∀ h:i≤ D,∃ W:ℝ, FaucetAndPose sym H D e v i h W (J i) L Hp 2 u 1 K 1 z)∧∀ i:ℕ,i≤ D→2*(measureV L Hp.e z)⁻¹≤ (J i).l ∧ 400*(measureV L Hp.e z)⁻¹ ≤ (J i).e:=by
     have ht(d:Fin (D+1)):∀ᶠ x in atTop,(∃ W:ℝ,FaucetAndPose sym H D e v d.val (Nat.le_of_lt_succ d.isLt) W (J d.val) L Hp 2 u 1 K 1 x)∧2 * (measureV L Hp.e x)⁻¹≤ (J d.val).l ∧400*(measureV L Hp.e x)⁻¹≤(J d.val).e:=by
          obtain ⟨W,hp,hS⟩:= ((eventually_ge_atTop (1:ℝ)).and (eventually_all.mpr (fun i:Stokes d.val=>eventually_all.mpr (fun j:Stokes d.val=> dawn e v (berth sym (H d.val) (Nat.le_of_lt_succ d.isLt) i j) hE)))).exists -- sig
          have ht(x:ℝ):Tendsto (fun z=>x * (measureV L Hp.e z)⁻¹) atTop (𝓝 0):=by simpa only [Function.comp_apply,mul_zero] using (tendsto_inv_atTop_zero.comp (tonicV L hL (show 0< Hp.e from by omega))).const_mul x
          have hg:Tendsto (fun x=>minorV L 1 x) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tonicV L hL (by omega)); filter_upwards [(ht 2).eventually_le_const (J d.val).breadth,(ht 400).eventually_le_const (J d.val).far,hg.eventually_le_const (show 0<(J d.val).ε/8 from div_pos (J d.val).light (by norm_num)), fig L Hp 2 u 1 K 1 e v W hL hu hHp hV (by omega) (by norm_num) hE hv hp] with z h1 h2 h3 h4; exact ⟨⟨W,hp,hS,h3,h4⟩,h1,h2⟩
     exact (eventually_all.mpr ht).mono fun x h=>⟨fun d hd=>(h ⟨_,Nat.lt_succ_of_le hd⟩).1,fun d hd=>(h ⟨_,Nat.lt_succ_of_le hd⟩).2⟩
end YM.Intag.Vale
#print axioms YM.Intag.Vale.dawnT
