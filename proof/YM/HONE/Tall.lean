import YM.Lyre.Advance
import YM.HONE.Bird
import YM.HONE.Bird
import YM.HONE.Pulse
import YM.HONE.Pulse
import YM.HONE.Stand
import YM.Lyre.Ascent
import YM.Lyre.Pillar
import YM.Lyre.Bloom
set_option autoImplicit false
noncomputable section
namespace YM.Intag.CardsT
open Function Filter Finset MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Lat QCD.Tide Push.GridApprox
open QCD.Grass QCD.Plum
open MassiveQCD MassiveQCD.Cupola MassiveQCD.Sample Sample.LoomT Sample.Quills
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
open scoped BigOperators Classical
variable {S:Scheme}{R:Side}{ℓ i k n:ℕ}{I:Type} [Fintype I] (A:Massive.Run S n R 6)
variable (X:I→ Cover) (U:I→ Averaging)(q:I→Bool)
local notation "H" k:arg=> Hole I S ℓ k
local notation "L" k:arg=> CardsT.link S ℓ k X
variable (w:∀ k:ℕ,Hole I S ℓ (k+1)→Hole I S ℓ k→ℝ)
variable (hw: ∀ k,ℓ ≤ k → SignedWeights S ℓ k X U (w k))
local notation "Sn"=> S.side R
set_option quotPrecheck false
variable (F:I → Cover → Insertion (S.side R n) 6) -- true ordered list tests
-- stage sensor.L.V ephemeral transport. choose left mass-density placement convention.

local notation "Pr"=>A.regulator.density
variable (Ψ:I → Cover → Insertion (S.side R k) 6)
variable (hA:A.Actual)(h:k≤n)
local notation "YC"=> fruitT A X U q w F Ψ
local notation "Qr" j:arg=> CardsT.stencil (I:=I) S ℓ j
local notation "VQ" jx:arg=> doubleT A X U F Ψ (i:=jx)
variable (hs:ℓ ≤ i)(hi:i≤ k)
open Massive.Patria.Rolls QCD.Tide Massive.Patria
local notation "κ"=> Tally
section rolls
variable {p:ℕ} -- p notation conflict
variable {Y Z:Type} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
variable (v:Signed) (Ux:Massive.Averaging)
lemma rotateF (Zq:Y→ₗ[ℝ]Z)(m:ℕ)(Ψ:Cover → Y)(Ω:Cover→ Z) (a b:Cover)(hp:Odd m)(ht:∀ z,Zq (Ψ z)=Ω (b+v.act z)) : Zq (Averaging.filter Ux m Ψ a)=Averaging.filter (Averaging.permute v Ux) m Ω (b+v.act a):=by
    let x:=fun z=> Ψ (z+a); let A:= b+v.act a; let y:=fun z=> Ω (z+A)
    have h:=stage_perm x v Zq y Ux (fun z=> by unfold x y; rw [ht, Signed.act_add]; apply congr_arg; unfold A; abel --] -- adapt
                                                               ) hp
    have hk : Averaging.filter Ux m x 0=Averaging.filter Ux m Ψ a:=by rw[roles,roles,show rolls 1 m (menu Ux) x 0=rolls 1 m (menu Ux) Ψ (0+a) from driftRoll _ _ _ _ a,zero_add]
    rw [hk] at h; refine h.trans ?_; rw [roles,roles, show rolls 1 m _ y 0=rolls 1 m _ Ω (0+A) from driftRoll _ _ _ _ A,zero_add]
lemma sculptA (a:Cover) (p:ℕ): v.act (p • a)=p • v.act a:=by induction p with| zero=>simp| succ p ih=>simp only [add_smul, Nat.succ_eq_add_one, one_smul,Signed.act_add, ih]
end rolls
open Cylinder
variable (C:∀ l:ℕ,Cells.Cut (S.side R l))(hC:(C ℓ).kind=.link)(hwC:∀ j,ℓ ≤ j→ j < n→ C (j+1)= gateH (C j) (QCD.Flume.sliceL (S.step j) (S.sides_next R j)))
local notation "Tn"=> C n
variable (U0:Averaging)(a b:Cover)(hv: CompleteP (C ℓ) b)
local notation "Φ"=>Signed.mirror (C ℓ).pos
local notation "Tz"=> b + Φ.act a
local notation "ρ" k:arg=> ratioTo S k ℓ
include hwC
lemma doors (hi:ℓ≤ i)(h:i≤ n): (C i).pos=(C ℓ).pos:=by induction hi with| refl=>rfl| @step i h' ih=>rw [hwC _ h' h]; exact ih (Nat.le_of_lt h)
include hv
lemma rarities (hi:ℓ≤ i)(h:i≤ n): CompleteP (C i) ((ρ i) • b):=by
     induction hi with
     | refl=> rw[centreN,one_smul]; exact hv
     | @step i hi ih=> rw [hwC i hi h, Column.chip _ hi,mul_smul]; exact soothing _ _ _ (ih (Nat.le_of_lt h)) ((S.step i).odd)
variable (X Y: Cover→ Insertion (S.side R n) 6)(hx:∀ p:Cover, Cylinder.Action.adj (C ℓ).pos ⇑(X p)=Y ((Signed.mirror (C ℓ).pos).act p))(hΩ:∀ a b:Cover,Massive.Patria.march b ⇑(Y a)=Y (a+b))
-- generic push. F.invariant alias. layer n physical pivot regulator
noncomputable def checkedT {Y:Type} [AddCommGroup Y][Module ℝ Y](U:Averaging)(m:ℕ)(x:Cover→Y)(a:Cover):Y:=Averaging.filter U m x (m • a)
local notation "Xb" m:arg=> checkedT U0 (ρ m)
local notation "Kq"=> C ℓ
-- linear on Borel reps
noncomputable def fenceT {c:Side}(p:Cells.Cut c): Stud c 6→ₗ[ℝ]Stud c 6:={toFun:= tallH p,map_add':=fun x y=>Lyre.road_add [p] x y,map_smul':=fun g x=> by exact Lyre.road_real [p] x g}
include hwC hv hx hΩ
-- Y may depend on a but claimed same all. native action & cuts committed in workspace.
lemma criesT (hm: ℓ≤ n): tallH (C n) (⇑(checkedT U0 (ρ n) X a))=⇑(checkedT U0 (ρ n) Y (b+(C ℓ).flip.act a)):=by
     let F:= (C ℓ).flip; let i:ℕ:=ratioTo S n ℓ; let g:=i • b; let Rv: Insertion (S.side R n) 6 →ₗ[ℝ] Stud (S.side R n) 6:= {toFun:=fun x=>x,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; let Z:= (fenceT (C n)).comp Rv
     have hp:= rarities C hwC b hv hm le_rfl; have h1:Odd i:=odd_to hm
     have ht(p:Cover): Z (X p)= Rv (Y (g+F.act p)):=by
          change tallH (C n) (⇑(X p))=⇑(Y (i • b+(C ℓ).flip.act p)); rw [Lyre.paintC (C n) (i • b) hp,doors C hwC hm le_rfl,hx p,hΩ,add_comm (i • b) ((C ℓ).flip.act p)]
     have h:= rotateF F U0 Z i X (fun x=>Rv (Y x)) (i • a) g h1 ht
     change Z _=Rv (_); refine h.trans ?_
     unfold checkedT; change Averaging.filter _ i _ _= _; rw [show Averaging.permute F U0=U0 from permit_mirror ..]; rw [roles,roles, rollLinear]; apply congr_arg; rw [smul_add]; unfold F g i; rw [sculptA] -- lemma
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.criesT
