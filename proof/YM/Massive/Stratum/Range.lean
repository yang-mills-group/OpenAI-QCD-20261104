import YM.Massive.Stratum.Crevice
import YM.Massive.Stratum.Summons
/-!
# Controller: spin and pure gauge prices

Stationary block step. Arrangement before any choice of the running beta tuning (and
no assertions about the latter here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{B T: Bed}{F L:Side→ℝ}
structure Rock (j:ℕ) where
  Z:Teller su
  beds:Train j→Bed
  D:ℝ
  signal:ℝ
  v:ℝ
  η:ℝ
  n:ℕ
  finiteGround:Side→ℝ
  loopGround:Side→ℝ
  lawful: Bedrock Z.bind Z beds D signal v η n finiteGround loopGround
variable (Q:Rock j)
lemma comes (K:KernelChoices)(j:ℕ)(hj:4≤j):∃ Q:Rock j, Q.Z.bind=K:=by
  obtain ⟨Z,V,D,γ,v,η,n,F,L,h⟩:= climate K j hj; exact ⟨⟨Z,V,D,γ,v,η,n,F,L,h.kernel.symm ▸ h⟩,h.kernel⟩

/-- Station state. Use another width field for generality; here
only impose a loop size bound for the pure (non-spin) page, width already fixed. -/
abbrev Town:= Mist.Ledger×Price
def loop (X:Town):ℝ:= X.2.bill+1
theorem ridge (X:Town):1 ≤ loop X:= le_add_of_nonneg_left X.2.good

def Loop (L:Side→ℝ)(E:Patch)(_ _: Mist.Ledger)(P Z:Price): Prop:= (P.bill+1)/2 ≤ Z.bill+1∧ L E.L ≤ Z.bill+1
lemma scope (L:Side→ℝ)(E:Patch)(X Y: Mist.Ledger):∃ M:Price,∀ P Z:Price,Price.Permit M P Z→ Loop L E X Y P Z:=by
  refine ⟨⟨1, |L E.L|,zero_lt_one,abs_nonneg _⟩,fun P Z h=>?_⟩
  have hx: |L E.L|+ P.bill/2 ≤ Z.bill:= h.2.2
  constructor <;> linarith [P.good,abs_nonneg (L E.L), le_abs_self (L E.L)]

variable (J:Plan j) -- for all blocks

def Flown (E:Patch) := Tangle (Story J J E Q.Z.bind Q.Z.top.clip Q.Z.top.width Q.v Q.Z.η Q.Z.C Q.Z.C) (Loop Q.loopGround E)
theorem regime (hj:4≤j): ∃ n:ℕ,∀ E:Patch,n≤E.L.val→ Century (Flown Q J E):=by
   have H:0 ≤ Q.Z.C:= zero_le_one.trans Q.lawful.bound
   obtain ⟨n,h⟩:= rays J J hj hj Q.Z.width H H; refine ⟨n,fun E ht=>?_⟩
   obtain ⟨P⟩:= Push.Uniform.pre_order su Q.Z.top.width Q.v E.J Q.Z.bind (le_refl 3)
   have hh:=h E ht _ Q.Z.bind Q.Z.top.width Q.v P Q.Z.top.clip; apply stitch _ _ hh
   · intro a b _ u; obtain ⟨X,H⟩:=scope Q.loopGround E a b; exact ⟨_, H _ _ (Price.step ..)⟩
   intro a ha; obtain ⟨X,H⟩:=scope Q.loopGround E a a; exact Price.hit X _ H

-- Cap boarded costs uniform in the train's choice.
def steering (S:Flight j j) (x:Train j) : Flight j j:= { S with wing:=x }
@[simp] lemma steers (S:Flight j j)(x): (steering S x).patch=S.patch:=rfl
@[simp] lemma gears (S:Flight j j)(x):(steering S x).L=S.L:=rfl
local notation "Qq" => Q.Z.top.clip
local notation "Kq" => Q.Z.bind
local notation "u₀" => Q.Z.top.width
structure Dispatch (S:Flight j j)(X Y:Town)(p:ChartRatio su)(c Θ:ℝ)(Ω:ParcelR):Prop where
  grain : 0 < c
  roofF : 1 ≤ Θ
  fares : Q.n≤ S.L.val
  owns : S.patch.Branches Q.Z.bind su
  applaud : Bonded J S.patch Q.Z.bind Q.Z.top.clip Q.Z.top.width Q.v Q.Z.η Q.Z.C Q.Z.C X.1 Y.1 Ω
  crossing : ∀ (z:Train j) (B T: Bed) (R:PathData su) (D:Towers S.L), let F:=steering S z;
    QuarryQ Qq Q.Z.η Q.η Q.Z.C B → QuarryQ Qq Q.Z.η Q.η Q.Z.C T → Enjoy B Qq u₀ Q.v (loop X) R →
    DeltaQ Kq Qq Q.Z.η Q.Z.C F B T D→∀ m:SparkMesh,reachM S.patch m →∃ (α:ℝ)(R':PathData su), Enjoy T Qq u₀ Q.v (loop Y) R' ∧ Nonempty (Summit F Kq m R' R Qq u₀ Q.v D p α c Θ Q.signal Q.D)

theorem signal_dispatch (X Y:Town) (S:Flight j j)(hf:Q.n ≤ S.L.val)(hp:LocalRatio p)(hv:S.patch.Branches Kq su)(h: Flown Q J S.patch X Y): ∃ c Θ Ω,Dispatch Q J S X Y p c Θ Ω:=by
   obtain ⟨Ω,hΩ⟩:= bonded J X.1 Y.1 Q.Z.width h.1
   obtain ⟨c,H1,H⟩:= uncover Q.lawful.tally hp Q.lawful.flour S.L
   let Θ:=max 1 (Q.finiteGround S.L)
   refine ⟨c,Θ,Ω,H1,le_max_left ..,hf,hv,hΩ,?_⟩
   intro i B T R D F hB hT hR hD m hm
   exact H F rfl hf hv _ _ D m _ _ _ Θ hB hT hD (ridge X) h.2.1 h.2.2 hm (le_max_right ..) hR
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.signal_dispatch
