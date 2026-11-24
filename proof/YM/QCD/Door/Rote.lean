import YM.QCD.Door.Iris
/-! # true hues rotate. No loss on valence. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks Fj
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{F:ℕ}
variable {Z:Ratio c f}{U V : Grid f}{E D J:Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {O:Send Z F D}{P:Rise f F E J}{p:OrbitG (Modes f F⊕Modes c F)}{r:OrbitG (Modes f F)}{q:OrbitG (Modes c F)}{s:Equiv.Perm (Site f)}{e:Equiv.Perm E}{j:Equiv.Perm J}{d:Equiv.Perm D}{t:ℝ}
variable (hv:Usher Z O U V p r q s d)(hp: Parade U V r P s e j t)
include hp hv
lemma root_N (i:Fj D E J): native O P (sail d e j i)=(native O P i).image s:=by
 cases i
 next i=>exact hv.treats i
 next i=>
    cases i
    next i=>exact hp.poseE i
    next i=>exact hp.current i
lemma brim_N (i:Fj D E J): brim O P (sail d e j i)=(brim O P i).image s :=by unfold Cove.brim; rw [root_N hv hp, halo_map _ hv.seps]
lemma bulge (W: Finset (Fj D E J)): brimW O P (W.image (sail d e j))=(brimW O P W).image s:=by
 unfold brimW; rw [biUnion_image,image_biUnion]; exact biUnion_congr rfl fun i _=>brim_N hv hp i
omit hv
lemma invacu (W: Finset J):P.wish (W.image j)=(P.wish W).image s:=by unfold Rise.wish; rw [biUnion_image,image_biUnion]; exact biUnion_congr rfl fun i _=>hp.inv _
lemma spared (W:Finset J): P.spare (W.image j) ↔ P.spare W:=by
 constructor
 · intro h k hk l hl hh
   have ht:=h (Finset.mem_image_of_mem (a:=k) j hk) (Finset.mem_image_of_mem (a:=l) j hl) (j.injective.ne hh); dsimp only at ht; rw [hp.current,hp.current,Finset.disjoint_image s.injective] at ht; exact ht
 intro h k hk l hl hh
 obtain ⟨k,hhk,rfl⟩:=mem_image.mp hk; obtain ⟨l,hhl,rfl⟩:=mem_image.mp hl; rw [hp.current,hp.current, Finset.disjoint_image s.injective]; exact h hhk hhl (fun he=>hh (congr_arg j he))
include hv
variable [Countable E][Countable J]
lemma hatch (T:Finset (Fj D E J)):q.passL (hue O P t T U)=hue O P t (T.image (sail d e j)) V:=by
   let i:=T.image (sail d e j); have ht: Cove.closeS O P t i V ↔ Cove.closeS O P t T U:=by
     unfold Cove.closeS i; rw [bulge hv hp,← hp.flags, (parts_map ..).2.2, invacu hp, ← image_inter _ _ s.injective]; exact (Finset.image_inj s.injective)
   have hf : P.spare (spent T) ∧ Cove.closeS O P t T U ↔ P.spare (spent i) ∧ Cove.closeS O P t i V:= by rw [show spent i=(spent T).image j from (parts_map ..).2.2, spared hp, ht]
   unfold hue; split
   next h=>rw [if_pos (hf.1 h)]; exact iris hv hp T
   next h=> rw [if_neg (mt hf.2 h),map_zero]
end YM.QCD.Sway
