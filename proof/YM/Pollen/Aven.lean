import YM.Pollen.Tulip
import YM.MassiveQCD.Mayer.Stamp
import YM.Pollen.Story
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c 6→L[ℂ]Fields c 6) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Z"=>Keys c 6
open ConnectedActivityE6 Blaze King
local notation "K"=> wag
local notation "T"=>Stitch.Tablet.credits
variable {J K':Type}
open Cape
local notation "H'"=> withdraw 6 o t
local notation "Q'" X:arg=> shutter Z X
namespace WindowU
variable (w₀ w₁:ℝ) (X:Grid c→EvenA c 6)
structure Given (p:Site c)(V: BudgetPoint)(t w w₀ w₁:ℝ)(X: Grid c→ EvenA c 6) :Prop where
    lease : ∃ (D:Type) (_ : Fintype D) (Y:D→ Support c)(x:D→Grid c→EvenA c 6)(f g:D→ℝ),
            X=∑ i,x i ∧ (∀ i,shadeG (x i))∧ (∀ i,p∈Y i)∧ (∀ i,Woven p (Y i) V t (x i) (f i))∧ Ac.Hit Y V.B f w w₀ ∧ Ac.Hit Y V.B g w w₁ ∧ ∀ i k, Creek.load (fun _=>t) (light _ (x i k)) ≤ g i -- unmask
variable {w₀ w₁} (k:Site c)
local notation "L"=>Given k U t w
variable (h: Given k U t w w₀ w₁ X) (Y :Grid c→EvenA c 6)
include h
namespace Given
lemma plies (hY: L v b Y) : L (w₀+v) (w₁+b) (X+Y):=by
    obtain ⟨F,hF,Sx,f1,f0,x,h1,h2,h3,h4,h5,h6,h7⟩:= h.lease; obtain ⟨J,hJ,Sy,f2,f',g',h1',h2',h3',h4',h5',h6',h7'⟩:=hY.lease
    refine ⟨F⊕J,inferInstance,Sum.elim Sx Sy,Sum.elim f1 f2,Sum.elim f0 f',Sum.elim x g',?_,fun i=> ?_,fun i=> ?_,fun i=> ?_, fun i=> Extra.Iteration.Cost.sum (h5 i) (h5' i), fun i=> Extra.Iteration.Cost.sum (h6 i) (h6' i),fun i=>?_⟩
    · rw [Fintype.sum_sum_type,h1,h1']; rfl
    · cases i; exact h2 _; exact h2' _
    · cases i; exact h3 _; exact h3' _
    · cases i; exact h4 _; exact h4' _
    cases i; exact h7 _; exact h7' _
lemma units (z:ℂ): L (‖z‖*w₀) (‖z‖*w₁) (z • X):=by
    obtain ⟨F,hF,Sx,f1,f0,x,h1,h2,h3,h4,h5,h6,h7⟩:= h.lease; let T'(i:F)(j:Grid c):= z • f1 i j
    have hh {b' :F→ℝ} {μ:ℝ} (hp:Ac.Hit Sx U.B b' w μ):Ac.Hit Sx U.B (fun i=>‖z‖*b' i) w (‖z‖*μ):=by
       intro i; convert budget_scale (norm_nonneg z) (hp i) using 1; funext j; split; next h0=> exact mul_assoc ..
       rw [mul_zero] -- indentation
    refine ⟨F,hF,Sx,fun i=>z • f1 i,_,_,?_,fun i U g=> ?_,h3,fun i=>Phased.complexTone (h4 _) z,hh h5,hh h6,fun i k=> ?_⟩; · rw[h1,smul_sum]
    · change slots 6 g (light _ ((z:ℂ) • _)) = light _ (z • _); rw[map_smul,map_smul,map_smul,h2]
    change _ ≤ ‖z‖*x i; dsimp only [Pi.smul_apply]; rw [map_smul,Creek.load_scale]; exact mul_le_mul_of_nonneg_left (h7 _ _) (norm_nonneg _)
lemma adoptsA (hv:w₀ ≤ v)(hb:w₁ ≤ b) : L v b X:=by obtain ⟨F,hF,Sx,f1,f0,x,h1,h2,h3,h4,h5,h6,h7⟩:= h.lease; exact ⟨F,hF,Sx,f1,f0,x,h1,h2,h3,h4,fun i=>budget_loosen (h5 i) hv,fun i=>budget_loosen (h6 i) hb,h7⟩
omit h
-- generic point.A finance.
variable (P':Set (Finset I))(F:I→ Grid c→ EvenA c 6)(hv:∀ i, Given (o i) U t w w₀ w₁ (F i))
local notation "ι"=> (Fintype.card I:ℝ)
include hv
lemma stakes (hp: 0 < t):∃ (D1 D2:Type)(_ : Countable D1)(_ : Countable D2)(R:Reel c 6 I D1)(Q:Lure c 6 I D2), CarryT o R Q U t w (ι*w₀) (ι*w₁) P' (vaultU F):=by
     choose J hJ Sx f1 f0 x h1 h2 h3 h4 h5 h6 h7 using fun j=>(hv j).lease
     let X' (i:Sigma J):= Sx i.1 i.2; let F'(i:Sigma J):= f1 i.1 i.2; letI :∀ i, Fintype (J i):= hJ; let M(j: Sigma J):=f0 j.1 j.2; let N(j: Sigma J):=x j.1 j.2
     have hIncome (g: (i:I)→ J i→ℝ) (C:ℝ)(hf:∀ i, Ac.Hit (Sx i) U.B (g i) w C): Ac.Hit X' U.B (fun i:Sigma J=>g i.1 i.2) w ((Fintype.card I:ℝ)*C):=by intro j; refine budget_finite (fun k=>(hf k.1 j).1 k.2) ?_ ; rw [Fintype.sum_sigma]; exact (sum_le_sum fun i hi=> budget_sum (hf i j) univ).trans_eq (by simp) -- sig
     have hz :∀ i:Sigma J, o i.fst∈ X' i:=fun i=> h3 i.1 i.2; let R:= astute o F' X' hz; refine ⟨Sigma J,Sigma J,inferInstance,inferInstance,R,_,statue o F' X' hz _ _ M P' (fun i=>h2 i.1 i.2) (fun i=>h4 i.1 i.2) N hp (hIncome x w₁ h6) (hIncome f0 w₀ h5) ?_ ?_⟩ -- `t' j` implicit fails annotate
     · intro i V; let x:= slipU i.fst (F' i V); exact Eq.trans_le (Stitch.Tablet.polite_bill {i.fst} _ (slated ..) hp) ((congr_arg (Creek.load (A:=Keys c 6) (fun _=>t)) (brand ..)).trans_le (h7 i.fst i.snd V)) -- scrape vs pluck
     intro i V; rw [h1]; exact (Finset.sum_apply V univ (f1 i)).symm
end Given
end WindowU
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.WindowU.Given.stakes
#print axioms YM.MassiveQCD.Sample.Basal.WindowU.Given.units
