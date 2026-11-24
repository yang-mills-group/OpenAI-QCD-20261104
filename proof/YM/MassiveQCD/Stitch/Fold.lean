import YM.MassiveQCD.Ribbon.Shifts
import YM.QCD.Cove.Aft
import YM.QCD.Loom.Palm
/-! # One source dictionary over an actual Rise. Geometry from unmarked zero books,
 may be padded. Every label E- or K-purchase, mask & arm. This is not any stochastic interpretation.
 No erasure of graded dignities even if measure projection annihilates an individual entry.
 Right marker convention (opposite to manuscript left). Leans on root-ledgers pre-paid at ALL
 required apertures; payable system defined in Loom and here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}
abbrev Tine (c:Side)(N:ℕ)(I:Type)[Fintype I]:= Patio (Keys c N⊕Spine I)
noncomputable def color (c:Side)(N:ℕ)(I:Type)[Fintype I](z:Lat.Frame c):Alg (Keys c N⊕Spine I)→L[ℂ] Alg (Keys c N⊕Spine I):= carry (Spine I) (slots N z).toLinearMap.toContinuousLinearMap
noncomputable def lights (s: Finset I)(X:Support c)(_o:I→Site c)(q:I→Bool)(x:Tine c N I): Prop:=Polite q s x∧clad (limits X) x.val -- o unused remove
structure Tablet (P:Rise f N E J)(I:Type)[Fintype I] where
   main : E→Grid f→ Tine f N I
   plug : J→Grid f→ Tine f N I
   spine : E→ Finset I
   shadow : J→ Finset I
variable {P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
structure Wave (t:ℝ)(q:I→Bool)(o:I→ Site f):Prop where
    use i: LocalOn (P.row i).support (X.main i)
    showAt i u : lights (X.spine i) (P.row i).support o q (X.main i u)
    measure i: Measurable (X.main i)
    oblige i: UsesFinal t (P.front i).place (X.plug i)
    chair i u: lights (X.shadow i) (P.front i).place o q (X.plug i u)
    budget i:Measurable (X.plug i)
    owes i u:(X.plug i u)≠0 → flags t u∩ (P.front i).place=(P.front i).inv
    spotE i: (X.spine i).image o ⊆ (P.row i).support
    spotK i: (X.shadow i).image o⊆ (P.front i).place
    turnsE: ∀ i U g, color f N I g (X.main i (gauge g U)).val =(X.main i U).val
    turnsK: ∀ i U g, color f N I g (X.plug i (gauge g U)).val =(X.plug i U).val
variable (t:ℝ)
open Fj
def read (u:Grid f)(i:E):= masked t (P.row i).support (X.main i) u
def dusk (u:Grid f)(w:Finset J):=if P.spare w ∧ P.wish w=flags t u then ∏ i∈w,X.plug i u else 0
def bluff (u:Grid f):= exp (∑' i,X.read t u i) * (∑' i,X.dusk t u i)
def made (u:Grid f)(s: Finset (Fj D E J)):= (∏ i∈leftE s,(NormedSpace.exp (X.read t u i)-1))*∏ j∈spent s,X.plug j u
variable {R:Ratio c f}
variable (G:Send R N D)(s:Finset (Fj D E J))
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
noncomputable def tunnel (u :Grid f) : Fields f N→L[ℂ]Fields c N:= (LinearMap.toContinuousLinearMap (wipe A B (G.shortP u)).toLinearMap).comp ((axle G u s).comp (LinearMap.toContinuousLinearMap (near A B).toLinearMap))
include P in
lemma tunnelP (u :Grid f)(x:Fields f N): tunnel G s u (grade x)=grade (tunnel G s u x):=by
    unfold tunnel; let F:=axle G u s; have he := forces G P u s; have hm(x): grade (F x)= F (grade x):=DFunLike.congr_fun he.evenG.symm.eq x
    change wipe _ _ _ (F (near _ _ _))= _; exact ((exterior_parity _ _).trans (congr_arg _ ((hm _).trans (congr_arg _ (exterior_parity _ x))))).symm -- unused P! choose ?
noncomputable def dye (u:Grid f): Tine c N I:=⟨carry S (tunnel G s u) (X.made t u s).val,evenCarry S _ (tunnelP (P:=P) G s u) _ (bright (X.made t u s))⟩
noncomputable def hue (u:Grid f): Tine c N I:= if P.spare (spent s) ∧ closeS G P t s u then X.dye t G s u else 0
variable {t}{q:I→Bool}{o:I→Site f}(hw:X.Wave t q o)
include hw
def markers (s:Finset (Fj D E J)):=((leftE s).biUnion X.spine) ∪ ((spent s).biUnion X.shadow)
lemma lights_read (u:Grid f)(i:E): lights (X.spine i) (P.row i).support o q (X.read t u i):=by
    unfold read; by_cases he:Healthy t (P.row i).support u
    · rw [masked_eq _ _ _ _ he]; exact hw.showAt i u
    rw [masked_ne _ _ _ _ he]; exact ⟨polite_nil ..,clad.nil _⟩
-- joint lands (Valuation carriers)
omit hw in
lemma candlehouse {J:Type} (p:J→ Patio X')(Q:J→Finset I)(s:Finset J)(U:Support f)(h:∀ i∈s,lights (Q i) U o q (p i)): lights (s.biUnion Q) U o q (∏ i∈s,p i):=by
    induction s using Finset.induction_on with
    | empty=> rw [biUnion_empty,prod_empty]; exact ⟨polite_empty_one _,clad.one _⟩
    | insert i s hi ih=> rw [biUnion_insert,prod_insert hi]; obtain ⟨hf,hF⟩:=h i (mem_insert_self ..); obtain ⟨hg,hG⟩:=ih (fun i hi=> h i (mem_insert_of_mem hi)); exact ⟨hf.attached hg,hF.mul hG⟩
lemma lights_made (s: Finset (Fj D E J))(u:Grid f): lights (X.markers s) (coreW G P s) o q (X.made t u s):=by
    let e i:= exp (X.read t u i)-1; let Y:= coreW G P s
    have h(i)(hi:i∈leftE s):lights (X.spine i) Y o q (e i):=by
        obtain ⟨hv,hF⟩:=X.lights_read hw u i; exact ⟨attire hv, hF.expR.raise (limitsMon _ _ (fun j hj=> mem_biUnion.mpr ⟨(.inr (.inl i)),by simpa [leftE] using hi,hj⟩))⟩
    let y i:=X.plug i u; have he(i)(hi:i∈spent s): lights (X.shadow i) Y o q (y i):=by
        obtain ⟨hv,hF⟩:=hw.chair i u; exact ⟨hv,hF.raise (limitsMon _ _ (fun j hj=>mem_biUnion.mpr ⟨(.inr (.inr i)),by simpa [spent] using hi,hj⟩))⟩
    obtain ⟨h1,h2⟩:= candlehouse e X.spine _ Y h; obtain ⟨h3,h4⟩:= candlehouse y X.shadow _ Y he; exact ⟨h1.attached h3,h2.mul h4⟩
end Tablet
end YM.MassiveQCD.Stitch
