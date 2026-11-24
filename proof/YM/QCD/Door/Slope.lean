import YM.QCD.Door.Rote
/-! # Pin lifts and Site Frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks OrbitG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{j k:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}{F:ℕ}
local notation "S"=> sliceL L H
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {G:Grid f→Sheet f}{δ a b c' q:ℝ}{l:ℕ} (P:Sun L c f H δ a b c' q l G)

lemma pivotal (F b:ℕ)(A' B' : Grid f)(U: Matrix (Modes f F) (Modes f F) ℂ)(V:Matrix (Modes c F) (Modes c F) ℂ)
    (p:Equiv.Perm (Site f)) (hp : ∀ i j,separation (p i) (p j)=separation i j) (hu:U∈unitary _)(hv:V∈unitary _) -- pivots
    (hx:∀ i:Support f,choir F (flowY P i A')=U * choir F (flowY P (i.image p) B')*star U)
    (hS:∀ i:Support f,choir F (heads P b i A')=U * choir F (heads P b (i.image p) B') * star V ∧ choir F (tailsF P b i A')=V* choir F (tailsF P b (i.image p) B') *star U)
    (hw: choir F (rL P b A')=U *choir F (rL P b B')*star V∧ choir F (rP P b A')=V*choir F (rP P b B')*star U):
    Usher S (P.equip F b) A' B' (trade (whole U V)) (trade U) (trade V) p (Equiv.sumCongr (Equiv.finsetCongr p) (Equiv.finsetCongr p)):=by
   have he i:Equiv.finsetCongr p i=i.image p:= Finset.map_eq_image ..
   refine ⟨hp,fun i=>?_,fun i x=>?_,fun x=>partitioned U V _,fun x=>?_⟩
   · cases i <;> exact he _
   · cases i
     next i=> change disguise (whole U V) (excess (pond _ (ship P.X i _)) x)=excess (pond _ (ship P.X (Equiv.finsetCongr p i) _)) _; rw [flowing,hx,he,flowing]; exact pondD ..
     next i=> change disguise (whole U V) (excess (bark (longP _ _ b _ i)) x)=excess (bark (longP _ _ b _ (Equiv.finsetCongr p i))) _; rw [he, big_eq,big_eq,(hS i).1,(hS i).2]; exact barkA U V _ _ hu hv x -- syntax
   rw [sea_eq,sea_eq,hw.1,hw.2]; exact barkW U V _ _ hu hv _

lemma podium {D V:Type*}[Fintype D][Fintype V](U:Matrix D D ℂ)(X:Matrix D V ℂ)(A' : Matrix V V ℂ)(F:ℕ): choir F (U*X*star A')= copies F U*choir F X *star (copies F A'):=by
 rw [choir_mul,choir_mul, Matrix.star_eq_conjTranspose,choir_star]; rfl

lemma remoteG (F b:ℕ)(X: Grid f)(u: Strut c)(d:Site f→ℂ)(p: Spike)(h : Warrant (raise S u) d p)(hs :Sacred P):
    let U:= copies F (TrU S u d p); let V:= copies F (TrV S u d p); let Q:=raiseS S u
    Usher S (P.equip F b) (sky (raise S u) X) X (trade (whole U V)) (trade U) (trade V) (act (raise S u)) (Equiv.sumCongr Q Q):=by
    intro U V Q
    apply pivotal _ F b _ X U V (act (raise S u)) (Push.Local.turn_sep _ _) (copies_unitary _ _ (trail h)) (copies_unitary _ _ (trail (mist _ _ h)))
    · intro i; rw [wool P hs h i]; rw [show raiseS S u i= i.image _ from Finset.map_eq_image ..]; exact podium ..
    · intro i; obtain ⟨he,hv⟩:= lane P b hs h i X; rw [he,hv,show raiseS S u i=i.image _ from Finset.map_eq_image ..]; exact ⟨podium ..,podium ..⟩
    obtain ⟨he,hv⟩:= shore P b hs h X; rw [he,hv]; exact ⟨podium ..,podium ..⟩

lemma range_id (Z :Type*):Equiv.sumCongr (Equiv.finsetCongr (Equiv.refl Z)) (Equiv.finsetCongr (Equiv.refl Z))=Equiv.refl (Finset Z ⊕ Finset Z):=by ext i; cases i <;> simp

lemma heatE (F b:ℕ)(X:Grid f)(k: Frame f):
 let U:=rotates F k; let V:= rotates F (k ∘ (S).embed)
 Usher S (P.equip F b) (gauge k X) X (trade (whole U V)) (trade U) (trade V) (Equiv.refl _) (Equiv.refl _):=by
 intro U V; rw [← range_id]; apply pivotal _ _ _ _ _ _ _ _ (fun i j=>rfl) (rotates_law ..) (rotates_law ..)
 · intro i; rw [mirr,(show i.image (Equiv.refl _)=i from Finset.image_id)]; exact podium ..
 · intro i; obtain ⟨he,hv⟩:=sets (P:=P) b k i X; rw [he,hv,(show i.image (Equiv.refl _)=i from Finset.image_id)]; exact ⟨podium ..,podium ..⟩
 obtain ⟨he,hv⟩:= sens (P:=P) b k X; rw [he,hv]; exact ⟨podium ..,podium ..⟩
lemma fluteE (F b:ℕ)(X: Grid f)(Z:Matrix (Flavor F) (Flavor F) ℂ)(hz:Z∈unitary _):
 let U:=flute (Row f) Z; let V:= flute (Row c) Z
 Usher S (P.equip F b) X X (trade (whole U V)) (trade U) (trade V) (Equiv.refl _) (Equiv.refl _):=by
 intro U V; rw [← range_id]; apply pivotal _ _ _ _ _ _ _ _ (fun i j=>rfl) (unit_f hz) (unit_f hz)
 · intro i; rw [(show i.image (Equiv.refl _)=i from Finset.image_id), column, Matrix.mul_assoc,(unit_f hz).2,Matrix.mul_one] -- image_id' ?
 · intro i; rw [(show i.image (Equiv.refl _)=i from Finset.image_id),column,column]; simp only [Matrix.mul_assoc,(unit_f hz).2,Matrix.mul_one,and_self]
 rw [column,column]; simp only [Matrix.mul_assoc,(unit_f hz).2,Matrix.mul_one,and_self]
end YM.QCD.Sway
