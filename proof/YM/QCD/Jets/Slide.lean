import YM.QCD.Cove.Vial
/-! # building Send from analytic Packs -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator

variable {F k j:ℕ}{c f:Side}{T:Ratio c f}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F

abbrev Tr (p : Side) := Support p ⊕ Support p
def headF (p:A):Site f:=p.1.1
def at_land {X:Land f (Site f) (Site f)}(i:Support f)(P:Kit.Pulse f): Sheet f:=Matrix.of fun a b=> X a.1 b.1 i P a.2 b.2 -- X implicit within def why

def ship (X:Land f (Site f) (Site f))(p : Support f)(Q:Kit.Pulse f):Matrix A A ℂ:= copies F (at_land (X:=X) p Q)

def foamB (u:Site f→Site c→ Bundle)(v:Site c→Site f→Bundle):Water c f F:= bladesF (choir F (Matrix.of fun (i:Row f)(j:Row c)=> u i.1 j.1 i.2 j.2)) (choir F (Matrix.of fun (i:Row c) (j:Row f) => v i.1 j.1 i.2 j.2))

lemma hook_eq (X: Land f (Site f) (Site f))(k:Support f)(P:Pulse f)(a b:A): ship X k P a b=if a.2=b.2 then X a.1.1 b.1.1 k P a.1.2 b.1.2 else 0:=rfl
lemma foamI (u:Site f→Site c→ Bundle)(v:Site c→Site f→Bundle)(i:A)(j:B): foamB u v (.inl i) (.inl j)= if i.2=j.2 then u i.1.1 j.1.1 i.1.2 j.1.2 else 0:=rfl
lemma foamR (u:Site f→Site c→ Bundle)(v:Site c→Site f→Bundle)(i:A)(j:B): foamB u v (.inr i) (.inr j)= if j.2=i.2 then v j.1.1 i.1.1 j.1.2 i.1.2 else 0:=rfl
@[simp] lemma foamRL (u:Site f→Site c→ Bundle)(v:Site c→Site f→ Bundle)(i:A)(j:B): foamB u v (.inr i) (.inl j)=0:=rfl
@[simp] lemma foamLR (u:Site f→Site c→ Bundle)(v:Site c→Site f→ Bundle)(i:A)(j:B): foamB u v (.inl i) (.inr j)=0:=rfl

def ater (g:Flight j k)(h:f.val=c.val*g.L.val) (u : Grid f) : Matrix B A ℂ:= choir F (tied g h 0 u)

lemma linked (s:Sheet f)(F:ℕ)(h:IsUnit s.det): copies F (s)⁻¹=(copies F s)⁻¹:=by
  apply Eq.symm; apply Matrix.inv_eq_right_inv; rw [← copies_mul,Matrix.mul_nonsing_inv _ h,copies_one]

lemma pond_comm {V W:Type*}[Fintype V][Fintype W](X Y: Matrix V V ℂ): Commute (pond (head V W) X) (pond (head V W) Y):=by
  unfold pond; apply finiteComm; intro i _; apply finiteComm; intro j _; refine timesComm ?_ (Y i j); apply Commute.mul_right; · exact (vpet (head V W) X (met (head V W) j)).symm
  exact (vpet (head V W) X (pet (head V W) i)).symm
lemma pond_add (Φ : Matrix A A ℂ)(K : Matrix A A ℂ)(T:Type*)[Fintype T]: pond (head A T) (Φ+K)=pond (head A T) Φ+pond (head A T) K:=by
  unfold pond; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; exact add_smul (Φ i j) (K i j) (Creek.v (met (head A T) j)*Creek.v (pet (head A T) i))
-- maybe F binder overrides

variable (X:Land f (Site f) (Site f))(Z: Land f (Site f) (Site c))(V: Land f (Site c) (Site f)) (r : ℕ)
def longP (Q:Kit.Pulse f) (i: Support f): Water c f F:= foamB (fun j k=> if i∈satZip j r then Z j k i Q else 0) (fun k j=> if i∈satZip j r then V k j i Q else 0)

def short (Q: Kit.Pulse f): Water c f F:= foamB (fun j k=> spoon Z j r j k Q) (fun k j=> spoon V j r k j Q)
def mapQ : Tr f→Pulse f→ EndA (Junta c f F):= Sum.elim (fun i Q=> pond (ha _ _ _) (ship X i Q)) (fun i Q=> bark (longP Z V r Q i))

lemma cash (U:Pulse f) (i v: Tr f) : Commute (mapQ X Z V r i U : EndA R) (mapQ X Z V r v U) := by
  cases i <;> cases v
  · exact pond_comm ..
  · exact pondB ..
  · exact (pondB ..).symm
  exact barkCom (heights A B) _ _
lemma cash_zero (P: Pulse f)(i: Tr f): excess (mapQ X Z V r i P) (1: Alg R)=0:=by
  rw [excess,ContinuousLinearMap.sub_apply]; cases i
  next i=> exact sub_eq_zero.mpr (nullVapply _ _)
  next i=> exact sub_eq_zero.mpr (ticks _)

end YM.QCD.Jets
