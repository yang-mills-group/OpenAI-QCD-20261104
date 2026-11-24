import YM.Elms.Corner
import YM.Pods.Cove
import YM.Pods.Rooms
/-!
# Drape spectators. Locality of every pose and anti-ordering at seam.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise ContDiff Stamp Kronecker Classical
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Romance
local notation "V"=> Lat.Fields n 6
local notation "Fω"=> Insertion n 6
variable (x:Drape)(l:List Axis)(Q:BudgetPoint)(z:ℝ)
variable {p:Label d}(Y: SourceRead.TaperHol)(W:Knot p)(h:Requisite Y p W)
include h
lemma readF : ∀ᶠ S: Stenc in atTop,∀ (n:Side)(P:Regulator n 6)(Q:BudgetPoint)(v:ℝ),∃ D:Cylinder.Formula S 6, poseEye W P Q v l=grant S D :=by
    have htX:= crestBorn _ (spoke h.mantle l); have htY:= crestBorn _ (spoke h.rent l)
    filter_upwards [htX,htY] with S hX hY n P Q v; obtain ⟨A,ha,_⟩:=hX.funded; obtain ⟨B,hb,_⟩:=hY.funded; rw [poseEye,layered,lawEv P h,← ha,←hb]; let b:ℂ:= (W.c P:ℂ); let r:ℂ:=(levyT W Q v:ℂ); refine ⟨r • (A+b • B),?_⟩; funext n o; symm; change Realize.placed S n o (r • (A+b • B)) = _; rw [map_smul,map_add,map_smul]; rfl
lemma fly (n:Side)(P:Regulator n 6)(Q:BudgetPoint)(v:ℝ)(k b:Cover): Patria.march b ⇑(poseEye W P Q v l n k)=⇑(poseEye W P Q v l n (k+b)):=by
     rw [poseEye,layered]; let f:= evoc (W.tool P) l; let t:ℂ:= (levyT W Q v:ℂ); have hx: Patria.march b ⇑(f n k)=⇑(f n (k+b)):= angleRoof W h l n P k b
     funext U; refine (show march b ⇑((t:ℂ) • (f n k: Insertion n 6)) U=t • march b ⇑(f n k) U from ?_).trans (congr_arg (t • ·) (congr_fun hx U)); unfold march TorusPCAC.Geometry.post; simp only [ContinuousMap.smul_apply,map_smul] -- signature
-- full spine mirror realization; notch bound in thermal chambers.
lemma attainsL (r:ℕ) : ∃ S:Stenc,∀ l:List Axis,l.length≤r→∀ (n:Side)(P: Regulator n 6)(O:BudgetPoint)(v:ℝ),∃ D:Cylinder.Formula S 6, poseEye W P O v l=grant S D:=by let W₀:= {l:List Axis|l.length≤r}; letI : Finite {l:List Axis // l∈ W₀}:= List.finite_length_le Axis r; obtain ⟨S,hS⟩:= (eventually_all.mpr fun i:W₀=> readF i.val Y W h).exists; exact ⟨S,fun l h=>hS ⟨l,h⟩⟩
omit h
noncomputable abbrev rim (k:ℕ)(o:Site n): Set (Site n):={x | separation o x≤k}
lemma shafts (S:Stenc):∃ k:ℕ,∀ n:Side,∀ o:Cover, ((fun x:Cover=> wrap n x+wrap n o) '' (S:Set Cover)) ⊆ rim k (wrap n o):=by
    obtain ⟨r,hr⟩:= (Permit.eventual S).exists
    refine ⟨r,fun n o z hz=>?_⟩; obtain ⟨u,hu,rfl⟩:=hz; exact marches _ _ _ hr hu
lemma padG {S:Stenc}(g:Cylinder.Formula S 6)(H:Set (Site n))(hx: (fun x:Cover=>wrap n x+wrap n o) '' (S:Set Cover) ⊆ H): Floors H (grant S g n o):= Romance.houses S _ H hx (grant S g n o) _ fun U=>rfl
include h
lemma shutters (r:ℕ): ∃ k:ℕ,∀ l:List Axis,l.length≤r→∀ (n:Side)(P: Regulator n 6)(O:BudgetPoint)(v:ℝ)(b:Cover), Floors (rim k (wrap n b)) (poseEye W P O v l n b):=by obtain ⟨S,hS⟩:= attainsL Y W h r; obtain ⟨k,hk⟩:= shafts S; refine ⟨k,fun l h n P O v b=>?_⟩; obtain ⟨D,hD⟩:= hS l h n P O v; rw [hD]; exact padG b D _ (hk n b)
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.shutters
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.fly
