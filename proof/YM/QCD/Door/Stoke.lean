import YM.QCD.Door.Twig
/-! # Orbit data. Ring mappers with stalks. -/
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
local notation "R"=> Junta c f F
variable {G:Grid f→Sheet f}{δ a b c' q t:ℝ}{l:ℕ} {P:Sun L c f H δ a b c' q l G} {D E J:Type}

structure OrbitG (A₀:Type*)[Fintype A₀] where
 φ: Dirac A₀ →+* Dirac A₀
 cont: Continuous φ
 even : ∀ x,φ (grade x)=grade (φ x)

namespace OrbitG
variable {A₀:Type*}[Fintype A₀]
def trade (X:Matrix A₀ A₀ ℂ) : OrbitG A₀ :=⟨(disguise X).toRingHom,(disguise X).toLinearMap.continuous_of_finiteDimensional,fun x=>(exterior_parity _ _).symm⟩
def spark (A₀:Type*)[Fintype A₀]: OrbitG A₀:=⟨rib _,surf_cont _,surf_grade⟩
def comp (p q:OrbitG A₀): OrbitG A₀:= ⟨p.φ.comp q.φ,p.cont.comp q.cont,fun x=>by simp only [RingHom.comp_apply,p.even,q.even]⟩
def dawn (X: Matrix A₀ A₀ ℂ): OrbitG A₀:=comp (trade X) (spark A₀)
def passL (V:OrbitG A₀): Patio (Pairs A₀) →+* Patio (Pairs A₀) where
 toFun x:= ⟨V.φ x.val, (V.even x.val).symm.trans (congr_arg V.φ x.property)⟩
 map_one':=Subtype.ext (map_one V.φ)
 map_zero':=Subtype.ext (map_zero V.φ)
 map_mul' x y:=Subtype.ext (map_mul V.φ x.val y.val)
 map_add' x y:=Subtype.ext (map_add V.φ x.val y.val)
lemma ph_p (V:OrbitG A₀)(x:Patio (Pairs A₀)): V.φ x.val=(V.passL x).val:=rfl
lemma phare (V:OrbitG A₀): Continuous V.passL:= (V.cont.comp continuous_subtype_val).subtype_mk _
end OrbitG

-- specified point path per X,X' opaque here. flags mapping. stamp. clean under.
structure Parade (U V:Grid f)(g: OrbitG A) (Z: Rise f F E J)(s:Equiv.Perm (Site f))(e:Equiv.Perm E)(j:Equiv.Perm J)(t:ℝ):Prop where
 flags : (flags t U).image s= RG.flags t V
 poseE i : (Z.row (e i)).support=(Z.row i).support.image s
 site i: (Z.row (e i)).site=s (Z.row i).site
 current i: (Z.front (j i)).place=(Z.front i).place.image s
 inv i: (Z.front (j i)).inv=(Z.front i).inv.image s
 ease i:g.passL (Z.main i U)=Z.main (e i) V
 voyage i:g.passL (Z.plug i U)=Z.plug (j i) V

-- with no reference to particular generator gauge sym, Ward per read.
structure Usher (S₀:Ratio c f)(G:Send S₀ F D)(U V:Grid f)(p: OrbitG (A⊕B))(a:OrbitG A)(b:OrbitG B)(s: Equiv.Perm (Site f)) (C:Equiv.Perm D):Prop where
 seps i j : separation (s i) (s j)=separation i j
 treats i: G.rooms (C i)=(G.rooms i).image s
 axle i x: p.φ (bucks G i U x)= bucks G (C i) V (p.φ x)
 rents x : p.φ (near _ _ x)=near _ _ (a.φ x)
 ships x: b.φ (wipe _ _ (G.shortP U) x)=wipe _ _ (G.shortP V) (p.φ x)

end YM.QCD.Sway
