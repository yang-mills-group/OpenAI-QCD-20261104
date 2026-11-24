import YM.MassiveQCD.Stitch.Mint
import YM.MassiveQCD.Ribbon.Dress
import YM.QCD.Door.Slope
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
open QCD.Sway QCD.Sway.OrbitG Finset
noncomputable def colors (I:Type)[Fintype I](z:Lat.Frame f)(N:ℕ): Alg (Keys f N⊕Spine I)→ₐ[ℂ] Alg (Keys f N⊕Spine I) where
 __ := (color f N I z).toLinearMap
 map_mul' x y:= ledger_alg (slots N z) (fun x=>(exterior_parity _ x).symm) x y
 map_zero' := map_zero (color f N I z)
 map_one':=by
    change carry _ _ 1=1; rw [show (1:Alg (Keys f N⊕Spine I))=stake (Keys f N) ∅ 1 from ((quiet ..).trans (map_one _)).symm]; rw [speaks,show LinearMap.toContinuousLinearMap (slots N z).toLinearMap 1=1 from map_one (slots N z)]
 commutes' x:=by
    simp only [Algebra.algebraMap_eq_smul_one]; -- goal?
    change color f N I z (x • 1)=x • 1; rw [map_smul]; unfold color; rw [show (1:Alg (Keys f N⊕Spine I))=stake (Keys f N) ∅ 1 from ((quiet ..).trans (map_one _)).symm]; rw [speaks,show LinearMap.toContinuousLinearMap (slots N z).toLinearMap 1=1 from map_one (slots N z)]
noncomputable def dance (I:Type)[Fintype I](z:Lat.Frame f)(N:ℕ): Tine f N I→ₐ[ℂ] Tine f N I:=car (colors I z N) fun _ he=> evenCarry _ _ (fun x=>(exterior_parity _ x).symm) _ he
abbrev Toned (G:Send R N D):Prop:=∀ U:Grid f,∀ z:Lat.Frame f, ∃ p: OrbitG (Modes f N⊕Modes c N),Usher R G (gauge z U) U p (trade (Lat.rotates N z)) (trade (Lat.rotates N (z∘ R.embed))) (Equiv.refl _) (Equiv.refl _)
theorem tonal {j k:ℕ}{L:YM.Next.Free.Flight j k}{H:f.val=c.val*L.L.val}{δ a b c' z':ℝ}{F:Grid f→Sheet f}{l:ℕ} (X: Jets.Sun L c f H δ a b c' z' l F)(N B':ℕ):Toned (X.equip N B'):=fun U z=> ⟨_,Sway.heatE X N B' U z⟩
lemma drivesAtG (U:Grid f)(z:Lat.Frame f)(h:Toned G)(s:Finset (Fj D E J))[Countable E][Countable J](x:Alg (Keys f N)):
    slots N (z∘ R.embed) (tunnel G s (gauge z U) x)=tunnel G s U (slots N z x):=by
        obtain ⟨p,h⟩:=h U z; let y:=(near A B x); have ht x': p.φ (axle G (gauge z U) s x')=axle G U s (p.φ x'):=by simpa only [Sway.sail, Equiv.sumCongr_refl,Equiv.coe_refl,Finset.image_id] using seal_ax h s (Equiv.refl _) (Equiv.refl _) x'; -- syntax
        change (trade (Lat.rotates N (z ∘ R.embed))).φ _ = wipe A B _ (axle G U s (near _ _ ((trade (Lat.rotates N z)).φ x))); exact (h.ships _).trans (congr_arg _ ((ht y).trans (congr_arg _ (h.rents x))))
include hw
lemma danceRead (i:E)(u:Grid f)(z:Lat.Frame f): dance I z N (X.read t (gauge z u) i)=X.read t u i:=by
   unfold read; by_cases he: Healthy t (P.row i).support u
   · rw [masked_eq _ _ _ u he,masked_eq _ _ _ _]; swap; · unfold Healthy; rw [gauge_flags]; exact he
     exact Subtype.ext (hw.turnsE ..)
   rw [masked_ne _ _ _ u he,masked_ne _ _ _ _,map_zero]; unfold Healthy; rw [gauge_flags]; exact he
lemma flopG (s:Finset (Fj D E J))(u:Grid f)(z:Lat.Frame f) : dance I z N (X.made t (gauge z u) s)=X.made t u s:=by
     unfold made; rw [map_mul,map_prod,map_prod]; congr 1
     · apply prod_congr rfl; intro i _; rw [map_sub,map_exp,map_one,danceRead X hw]; exact (dance I z N).toLinearMap.continuous_of_finiteDimensional
     exact prod_congr rfl fun i _=>Subtype.ext (hw.turnsK ..)
lemma insulated (U:Grid f)(z:Lat.Frame f)(h:Toned G)(s:Finset (Fj D E J))[Countable E][Countable J] : dance I (z∘ R.embed) N (X.hue t G s (gauge z U))=X.hue t G s U:=by
    unfold hue Cove.closeS; rw [gauge_flags]; split; swap; · exact map_zero _
    apply Subtype.ext; change carry S _ (carry S _ _)= carry S _ _; apply vista (Keys c N); intro i; have ht:= flopG X hw s U z; rw [wing,wing,wing];
    rw [show LinearMap.toContinuousLinearMap _ _=_ from drivesAtG G U z h s (scrape (Keys f N) i (light X' (X.made t (gauge z U) s)))]; congr 1
    exact (wing S _ i _).symm.trans (congr_arg _ (congr_arg Subtype.val ht)) -- check ↑
end Tablet
end YM.MassiveQCD.Stitch
