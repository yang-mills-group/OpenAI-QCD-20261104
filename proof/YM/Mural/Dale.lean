import YM.Mural.Relay
/-! # Script of expenditures with synchronized index shape. -/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false
namespace YM.MassiveQCD.Plette
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace Push.AbsoluteSums
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG PaletteT
open scoped BigOperators Topology Classical ContDiff
variable {c L:Side}(N:ℕ)(p:Unit→Site c)(q:Unit→Bool){I J V D E K:Type}[Fintype I] (F:Patron.Rail c (ample N Unit) J)(Y:Ruby.Hue c N D)(X:Ruby.Hue c N V)(Z:Ruby.Hue c N E) (P:Patron.Rail c N K)(O:BudgetPoint) (t a b r v:ℝ) {w:ℝ}
open Plate.Film Patron QCD.Finch Kites Ruby
variable (U:Option I→ J→Grid c→ EvenA c (ample N Unit))(Zt:Support c)(κ:Delta I)(g: Lat.Frame c)
open Acre Acre.Rails Acre.Rails.Links
set_option maxHeartbeats 480000 in
lemma limE (j:Option I) (Y: Ruby.Hue c (ample N Unit) D) : toEnv (Trail Y (pathsV N F (U j)) t)= toEnv (pathsV N (Trail Y F t) (portH N F U Y j t)):=rfl
lemma onward (i:Option I) : toEnv (limb N p a t r Y (pathsV N F (U i)) b)= toEnv (pathsV N (limb N p a t r Y F b) (pulseV N p t F U Y a b r i)):= by
    let Z1:=pursue N p a F t r; let V i:=pursue N p a (pathsV N F (U i)) t r; let Z:=radial Unit Y; let R i:=(V i).warp
    refine Eq.trans (b:= toEnv (Trail Z (pathsV N Z1 (R i)) b)) (?_) (limE N Z1 b R i _)
    refine congr_arg (fun F:Rail c (ample N Unit) J => toEnv (Trail Z F b)) (show V i= pathsV N Z1 (R i) from rfl)
set_option quotPrecheck false
local notation "Fa" => limb N p a t 1 Y F O.threshold
local notation "Fb" => limb N p v a r X Fa O.threshold
local notation "Fc" => limb N p v v 1 Z Fb O.threshold
noncomputable def pulseF :=let R:=pulseV N p t F U Y a O.threshold 1; let R':=pulseV N p a (Fa) R X v O.threshold r; pulseV N p v (Fb) R' Z v O.threshold 1
local notation "V★"=> pulseF N p F Y X Z O t a r v U
variable (hP:Parade N p t F U q Zt g κ)(ht:0<t)(ha:0<a)(hv:0<v) (hκ:PaletteT.straight κ)(h1:∀ i,shadeG (Y.mean i))(h2:∀ i,shadeG (X.mean i))(h3:∀ i,shadeG (Z.mean i))
include hP ht ha hv hκ h1 h2 h3
lemma revenuesR : Parade N p v (Fc) (V★) q Zt g κ:=by
   let R:=pulseV N p t F U Y a O.threshold 1; let R':=pulseV N p a (Fa) R X v O.threshold r
   have hQ:= advanceR N p t F U q Zt g κ Y a O.threshold 1 hP ha ht hκ h1
   have hw:= advanceR N p a Fa R q Zt g κ X v O.threshold r hQ hv ha hκ h2
   exact advanceR N p v Fb R' q Zt g κ Z v O.threshold 1 hw hv hv hκ h3
omit hP ht ha hv hκ h1 h2 h3
lemma incomeZ (b0 a0 r0:ℝ)(O:BudgetPoint)(F:Patron.Rail c (ample N Unit) K)(G: Patron.Rail c (ample N Unit) E)(hp:toEnv F=toEnv G) : toEnv (limb N p b0 a0 r0 Y F O.threshold)= toEnv (limb N p b0 a0 r0 Y G O.threshold):=congr_arg (fun X:Envelope c (ample N Unit)=>toEnv (limb N p b0 a0 r0 Y X.snd O.threshold)) hp
lemma chart (i:Option I) : toEnv (limb N p v v 1 Z (limb N p v a r X (limb N p a t 1 Y (pathsV N F (U i)) O.threshold) O.threshold) O.threshold)= toEnv (pathsV N (Fc) ((V★) i)):= by
   let R:=pulseV N p t F U Y a O.threshold 1; let R':= pulseV N p a (Fa) R X v O.threshold r; let A:=pathsV N F (U i); let C1:=limb N p a t 1 Y A O.threshold; let f1:= pathsV N Fa (R i); let C2:=limb N p v a r X C1 O.threshold; let f2:=pathsV N Fb (R' i)
   have hh: toEnv C1=toEnv f1:= Plette.onward N p F Y t a O.threshold 1 U i
   have hv: toEnv C2=toEnv f2:= (incomeZ N p X v a r O C1 f1 hh).trans (Plette.onward N p Fa X a v O.threshold r R i)
   exact (incomeZ N p Z v v 1 O C2 f2 hv).trans (Plette.onward N p Fb Z v v O.threshold 1 R' i)

end YM.MassiveQCD.Plette
#print axioms YM.MassiveQCD.Plette.chart
