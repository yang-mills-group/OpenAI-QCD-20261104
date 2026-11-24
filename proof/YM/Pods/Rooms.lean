import YM.Pods.Cove
import YM.Massive.Lining.Cameo
/-!
# Supplies for every actual primary stencil along this path

Here deterministic estimate, prices the entire calibration surface BEFORE estimate
of the values of the mix. Applies to single fields and their simultaneous actual moments.
(This is an instance: not abstract probe assumptions.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Romance
open QCD QCD.Lat QCD.RP QCD.Grass Lattice Wilson MeasureTheory Function Filter Finset NormedSpace
open Chess Cells Tiling Tide QCD.Flume
open scoped BigOperators Topology Matrix.Norms.L2Operator ComplexOrder ContinuousMap
variable {A : Type*} {n : Side} {F : ℕ} {x y : Insertion n F}
variable {p k r m:ℕ} (T : Tiling n) (V : Insertion n F→ₗ[ℂ]ℂ)(R: Regulator n F) {J:RG.Patch}{e:ℝ}
open UV Lining Lining.Temper Cylinder
-- factor each set-local R-place through the grid Loc without addition of any support
section geom
variable (S:Finset Cover)(b:Cover)
local notation "D"=> Nearest S 6
local notation "Gf"=> Dirac (Nearest S 6)
local notation "Ap"=> (lower (n:=n) (S:=S) (F:=6) b)
local notation "Ω"=> ((fun x:Cover=>wrap n x+wrap n b) '' (S:Set Cover) : Set (Site n))
local notation "Tk"=>RP.Deck Ω 6
noncomputable def beamslot (x: D) : Modes n 6 := ((wrap n (x.1.1.val+b),x.1.2),x.2)
noncomputable def taxG (n:Side)(x:D):ℂ:=ap n (x.1.1.val+b)
noncomputable def diagonalL (n:Side):= Matrix.diagonal (taxG S b n)
theorem tax_price (n:Side)(x:D) : ‖taxG S b n x‖=1:=by simp [taxG,ap,norm_prod]
lemma ferryT (i:D): adapter (Ap) Ap (psi i)= taxG S b n i • psi (beamslot S b i):=by
    rw [adapt_psi]; suffices h:∑ j:Modes n 6,(if beamslot S b i=j then taxG S b n i else 0) • psi j= _ from h; simp only [ite_smul,zero_smul]; rw [Finset.sum_ite_eq, if_pos (mem_univ _)]
lemma ferryB (i:D): adapter (Ap) Ap (bar i)= taxG S b n i • bar (beamslot S b i):=by
    rw [adapt_bar]; suffices h:∑ j:Modes n 6,(if beamslot S b i=j then taxG S b n i else 0) • bar j= _ from h; simp only [ite_smul,zero_smul]; rw [Finset.sum_ite_eq, if_pos (mem_univ _)]
lemma houses (W:Set (Site n))(hW:Ω ⊆ W) (x:Insertion n 6)(f:Cylinder.Formula S 6)(he:∀ U, x U= places b f U): Floors W x:=by
    have ht(x: D): (beamslot S b x).1.1∈ Ω:=⟨x.1.1,x.1.1.property,(map_add (wrap n) _ _).symm⟩; let g:D→(RP.Deck W 6):= fun x=> ((⟨(beamslot S b x).1.1,hW (ht x)⟩, x.1.2),x.2); let D':=diagonalL S b n; let F:= (Grass.pass g).comp (adapter D' D')
    let Z:= fun (V:Grid n)=> porch S (expandAt (wrap n b) V) f
    have h:LocalOn Ω Z:=LocalOn.expandAt (S:Set Cover) (fun V:CoverConfig su=> porch S V f) (fun U V h=>?_ ) (wrap n b)
    rotate_left
    · change porch S U f=porch S V f; unfold porch; rw [show Source.entry (S:=S) U=Source.entry V from funext (fun i=> by unfold Source.entry; rw [h _ i.1.property.1 i.1.property.2])]
    have hz (i : Nearest S 6) : (setDay W) (g i) = beamslot S b i:= rfl
    have hF : adapter Ap Ap=(Grass.pass (setDay W)).comp F:=by
       apply ext_atoms; rintro (i|i)
       · change adapter Ap Ap (psi i)= Grass.pass (setDay W) (Grass.pass g (adapter D' D' (psi i))); rw [ferryT, adapt_psi]; simp only [D', diagonalL,Matrix.diagonal_apply,ite_smul,zero_smul,sum_ite_eq,mem_univ,↓reduceIte,map_smul,pass_psi,hz] -- sum_ite_eq check
       change adapter Ap Ap (bar i)= Grass.pass (setDay W) (Grass.pass g (adapter D' D' (bar i))); rw [ferryB,adapt_bar]; simp only [D', diagonalL,Matrix.diagonal_apply,ite_smul,zero_smul,sum_ite_eq,mem_univ,↓reduceIte,map_smul,pass_bar,hz]
    refine ⟨F ∘ Z,F.toLinearMap.continuous_of_finiteDimensional.comp ((porch_c S f).comp (show Continuous (expandAt (wrap n b) (K:=su.El)) from by unfold expandAt; fun_prop)),fun U V hv=> congr_arg F (h U V (agrees_mono hv hW)),fun U=>?_⟩
    rw [he,places,hF]; rfl
lemma places_floor (x:Insertion n 6)(f:Cylinder.Formula S 6)(he:∀ U, x U= places b f U): Floors Ω x:= houses S b _ (fun _ hx=>hx) x f he
end geom
end YM.Massive.Romance
#print axioms YM.Massive.Romance.places_floor
