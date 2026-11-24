import YM.Clink.Vilax
import YM.Lapin.Zink
import YM.Kai.Rind
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria
open QCD Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf QCD.Orbit Quarry Garden Bay Run QCD.Jets.Sun Pine Grass Lat
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails
open PCAC PCAC.Oren Patria Patria.Gall
open MassiveQCD.Sample.Basal MassiveQCD.Sample.Basal.Surge
open Massive.Patria.Depth
variable {S: Scheme}{R: Side}{n r q d:ℕ}{A: Run S n R 6}{U:BudgetPoint}
local notation "M"=> S.side R r
variable (B:ℕ)(V:(c:Side)→ Surge c)(o:Cover)(D:Cover→Insertion (S.side R r) 6)(u:Averaging)
open QCD.Acre.Rails.Reference
lemma earnsR (c:Side)(h:M=c) (U:Massive.Density c 6)(T:Massive.Run S n R 6)(hp:(⇑(actor T r):Massive.Density M 6)=transit h.symm U) (hx: ∀ b:Cover, (V M).eats (⇑(actor T r)) b= (⇑(D b):Massive.Density M 6)): transit h (Patria.Depth.report T D u r o) = (V c).eats U o:=by
        rw [Patria.Depth.arrivesHere, ←hx, hp]; subst c; rfl
end YM.Massive.Patria
#print axioms YM.Massive.Patria.earnsR
