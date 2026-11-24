import YM.Mural.Keel
/-! # Purchase identities for packed open line and propagation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side} {j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
variable {I E:Type}(D:DeckV c N)(D':DeckV f N)(L: YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
variable (Z:PrintR f N Rank I E)
local notation "S'"=> (L.visit K d)
local notation "WE"=> DeckV.emblem
variable {Ic Ec:Type}(P: PrintR c N Rank Ic Ec)(C:ℂ)(Φ:Option Rank→Grid f→ Grid c→ℂ)
open QCD.Jets
local notation "sendV"=> Transfer.blockMap L K d β r hk
local notation "Ξ"=> (blankR f N)
variable {z α:ℂ}{y:ℝ}{S:Support c}
local notation "K₀"=> Keys f N
local notation "K₁"=> Keys c N
variable (W: Insertion f N)
variable (A B: Grid f→Mat)
noncomputable def cubeQ (i:Rank) : Grid f→ℂ:= fun U=> A U i.fst i.snd
noncomputable def scaleLoad (i:Rank)(ha:Continuous A): Insertion f N:= ⟨fun U=> cubeQ A i U • W U,by unfold cubeQ; exact ((continuous_apply _).comp ((continuous_apply _).comp ha)).smul W.continuous⟩
-- Scalar weight in messages fixed per step.
variable (hw:∀ V, W V= α • D'.density V)
lemma paintD (X: Insertion f N)(p:ℂ)(V:Grid c): sendV (p • X) V=p • sendV X V:=congr_arg (fun x:Insertion c N=> x V) (map_smul ..)
-- delivery of blank birth with regular and forced. start.
variable (x y:Site c)(p q:Site f)
local notation "ℒ"=> loaded p q L d x y
local notation "Cq"=> cleared p q L d x y
local notation "T!"=>texel L d 0 x p
local notation "U!"=>texel L d 0 y q
local notation "δp"=> (shadeM L d x y p q z)
private lemma noTop (i:Option Rank)(U:Grid f)(h: ∀ j,Summable (fun i=> ‖D'.K.warp i j‖)): D'.emblem (blankR f N) i sD U=0:=by
   let H:= blankR f N; let p:= (fun _ :Unit=> (0:Site f)); have hv:=blank_fides (N:=N) p D'.O ∅ (fieldD 0 0); have he: H.regE i= H.regE none:= by
       suffices hh':∀ X Y:Reel f N Unit PEmpty,X=Y from hh' _ _; rintro ⟨x,y,z⟩ ⟨u,v,w⟩; congr <;> funext i<;>exact PEmpty.elim i
   have ht: H.regK i= H.regK none:=by suffices he:∀ X Y:Film f N Unit PEmpty,X=Y from he _ _; rintro ⟨x,y,z⟩ ⟨u,v,w⟩; congr<;>funext i<;>exact PEmpty.elim i
   unfold DeckV.emblem; rw [he,ht]; exact rosa H U D'.O ∅ p _ D'.K D'.E (h U) hv -- `rw he ht` defin
variable (hA: Strike D D' L d K r β (blankR f N) P C (shadeM L d x y p q z))
include hk hA hw
lemma pioneer (ha: ∀ i: Option Rank,∀ U:Grid f, D'.emblem (blankR f N) i ∅ U=D'.density U)(hb:∀ U,Summable fun i=> ‖D'.K.warp i U‖) (i:Rank)(U:Grid c) :
   z • (sendV (scaleLoad W ℒ i (loaded_c ..)) U - Cq U i.1 i.2 • (sendV W U)) =α • C • WE D P (some i) sD U:=by
   let A:=ℒ; let v:= scaleLoad W A i (loaded_c ..); let k :ℂ:= (cleared p q L d x y U) i.fst i.snd
   let T:= v-k • W; let g:= shadeM L d x y p q z (some i)
   let Θ(V:Grid f):= Kit.sheath 1 (ater (F:=N) L d V); let u(V:Grid f):=g V U • (Θ V (D'.density V))
   have hΩ(X:Grid f)(c:ℂ)(x: Fields f N): Θ X (c • x)= c • Θ X x:=congr_fun (Transfer.soften_smul L d (fun _=>x) c) X
   have hx(X:Grid f):Θ X 0=0:=by simpa using hΩ X 0 0 -- zero rhs.Y
   have ht:=hA.roll (some i) U sD
   let ψ:=engine r K₁
   have hp: ψ ((S').push β u U)= C • WE D P (some i) sD U:=by
        refine Eq.trans ?_ ht; apply congr_arg ψ; apply congr_arg (fun f=> (S').push β f U); funext a; rw [if_pos rfl,noTop D' (some i) a hb,ha]; change u a= Θ a 0 +_; rw [hx, zero_add]
   have hQ(X:Grid f) : Θ X ((z • T) X)= α • u X := by
       have hZ: g X U= z*(A X i.1 i.2-k):=rfl
       change Θ X (z • (cubeQ A i X • W X-k • W X))=_
       unfold cubeQ u
       rw [hw,← sub_smul,←mul_smul, smul_comm _ α,hΩ,hZ,hΩ]
   have h: z • (sendV v U-k • sendV W U)= sendV (z • T) U:=by
        rw [paintD L d K,show sendV T U=sendV v U-sendV (k • W) U from congr_arg (fun x: Insertion c N=> x U) (map_sub ..),paintD L d K]
   rw [h, extendT L d K r β hk _ _ hQ]; refine Eq.trans ?_ (congr_arg (α • ·) hp)
   unfold StepData.push; simp_rw [smul_comm _ α]; rw [integral_smul,map_smul]
end YM.QCD.Comet
#print axioms YM.QCD.Comet.pioneer
