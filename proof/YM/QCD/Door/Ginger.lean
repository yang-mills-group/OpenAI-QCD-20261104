import YM.QCD.Door.Winds
/-! # effective innovation matrices. Frames rotate each reading, chiral-star might couple BOTH. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{j k:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}{F:ℕ}
local notation "S"=> sliceL L H
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {G:Grid f→Sheet f}{δ a b c' q:ℝ}{l:ℕ} (P:Sun L c f H δ a b c' q l G)

def openK (X:Site f→Site c→Bundle): ArrayL (Site f) (Site c):= Matrix.of fun i j => X i.1 j.1 i.2 j.2

def seatL (b:ℕ)(i:Support f)(U:Grid f)(x:Site f)(y:Site c):Bundle:= if i∈ satZip x b then P.Z x y i (settled U) else 0
def seatV (b:ℕ)(i:Support f)(U: Grid f)(y:Site c)(x:Site f):Bundle:= if i∈satZip x b then P.V y x i (settled U) else 0

def seatS (b:ℕ)(U:Grid f)(x:Site f)(y:Site c):Bundle:=spoon P.Z x b x y (settled U)
def seatA (b:ℕ)(U:Grid f)(y:Site c)(x:Site f):Bundle:=spoon P.V x b y x (settled U)

def flowY (i : Support f)(U: Grid f):Sheet f:= at_land (X:=P.X) i (settled U)
abbrev heads (b:ℕ)(i:Support f)(U:Grid f):=openK (seatL P b i U)
abbrev tailsF (b:ℕ)(i: Support f) (U:Grid f):=openK (seatV P b i U)
abbrev rL (b:ℕ)(U:Grid f):=openK (seatS P b U)
abbrev rP (b:ℕ)(U:Grid f):=openK (seatA P b U)
lemma sea_eq (b:ℕ)(U:Grid f): (P.equip F b).shortP U= bladesF (choir F (rL P b U)) (choir F (rP P b U)):=rfl
lemma big_eq (b:ℕ)(i:Support f)(U:Grid f): (longP P.Z P.V b (settled U) i: Water c f F)=bladesF (choir F (heads P b i U)) (choir F (tailsF P b i U)):=rfl
lemma flowing (i: Support f)(U:Grid f): ship P.X i (settled U)= choir F (flowY P i U):=rfl

-- covariance comp Cell.
lemma whist {W V:Type*} {X Y:ArrayL W V}(h:∀ x y,cell X x y=cell Y x y): X=Y:=by ext ⟨x,a⟩ ⟨y,b⟩; exact congrFun (congrFun (h x y) a) b

lemma plated (M:Site f→Site c→Bundle)(N:Site f→Site c→Bundle)(f:Frame f)(g:Frame c)(h:∀ i j,M i j=touch (colour (f i))*N i j*star (touch (colour (g j)))) : openK M=siteRot f * openK N * star (siteRot g):=by
 apply whist; intro i j; unfold siteRot; rw [cell_ride_right,cell_ride_left]; exact h i j

variable {P}
lemma mirr (K:Sun L c f H δ a b c' q l G)(k:Frame f)(i:Support f)(U:Grid f): flowY K i (gauge k U)=siteRot k *flowY K i U *star (siteRot k):=by
  exact plated (fun x y=> K.X x y i (settled (gauge k U))) (fun x y => K.X x y i (settled U)) k k fun x y =>(K.X0.crop x y i).2.2.2.2.2 _ k
lemma sets (b:ℕ)(k:Frame f)(i:Support f) (U:Grid f): heads P b i (gauge k U)=siteRot k * heads P b i U*star (siteRot (k ∘ (S).embed)) ∧ tailsF P b i (gauge k U)=siteRot (k∘(S).embed)*tailsF P b i U*star (siteRot k):=by
  constructor
  · apply plated; intro x y; unfold seatL; split; · exact (P.Z0.crop x y i).2.2.2.2.2 U k
    simp
  apply plated; intro y x; unfold seatV; split; · exact (P.V0.crop y x i).2.2.2.2.2 U k
  simp
lemma sens (b:ℕ)(k : Frame f)(U:Grid f): rL P b (gauge k U)=siteRot k*rL P b U *star (siteRot (k∘(S).embed))∧ rP P b (gauge k U)=siteRot (k ∘(S).embed)*rP P b U*star (siteRot k) := ⟨plated _ _ k _ fun i j=> (trimming P.Z0 i b i j).2.2.2.2.2 U k, plated _ _ _ k fun i j=> (trimming P.V0 j b i j).2.2.2.2.2 U k⟩
end YM.QCD.Sway
