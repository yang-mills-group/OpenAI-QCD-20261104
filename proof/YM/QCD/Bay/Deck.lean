import YM.QCD.Jets.Guide
import YM.Push.LOCAL_SPLITTING.Orientation
/-! # Motion at both layers. Choose spin and seam lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{f c: Side}

abbrev Strut (n: Side):= Signed×Site n
namespace Strut
variable {p: Signed}
-- no group instance on Strut to avoid diamonds; instead explicit product & reindex. action

def act (s: Strut f):= shiftE s.1 s.2
def sky (s: Strut f)(U:Grid f):= pull s.1 s.2 U
def pod (u v: Strut f): Strut f:= (u.1*v.1, affine u.1 u.2 v.2)
lemma podA (u v:Strut f): act (pod u v)= (act v).trans (act u):=by ext1 x; change affine (u.1*v.1) (affine u.1 u.2 v.2) x=affine u.1 u.2 (affine v.1 v.2 x); simp [affine, Signed.act_mul,add_assoc]
lemma skying (u v: Strut f)(U:Grid f): sky v (sky u U) = sky (pod u v) U:=pull_pull ..

def skyEquiv (v:Strut f):Equiv.Perm (Strut f):=⟨pod v,fun w=>(v.1⁻¹*w.1,(act v).symm w.2),fun w=> Prod.ext (inv_mul_cancel_left v.1 w.1) ((act v).symm_apply_apply _),fun w=> Prod.ext (mul_inv_cancel_left v.1 w.1) ((act v).apply_symm_apply _)⟩

def raise (S:Ratio c f) (w: Strut c):Strut f:= (w.1,S.embed w.2)
lemma ups (u v:Strut c)(S:Ratio c f): raise S (pod u v)=pod (raise S u) (raise S v):=by refine Prod.ext rfl ?_; exact (root_affine ..).symm
lemma peaks (u:Strut c)(S:Ratio c f)(x : Site c): act (raise S u) (S.embed x)=S.embed (act u x):=root_affine ..

variable {s v u:Strut f}
def Warrant (s:Strut f)(u:Site f→ℂ)(V:Spike):= Glare s.1 0 0 s.2 u ∧ Swing s.1 V
-- push proof-equal action
variable {g h: Site f→ℂ}{A B : Spike}

def lightP (s: Strut f)(T:Spike) (u:Site f→ℂ)(i:Site f): Bundle:= u i • wave (star T)
abbrev haze (s:Strut f)(T: Spike)(u:Site f→ℂ):= hues s.2 s.1 u T
lemma secure (s:Strut f):∃ V B,Warrant s V B:=by obtain ⟨v,h⟩:=shades s.1 0 0 s.2; obtain ⟨p,hp⟩:= Swing.goes s.1; exact ⟨v,p,h,hp⟩
lemma trail (h:Warrant u g A):haze u A g∈unitary _:=colour_wheel h.1 h.2
lemma license (h:Warrant u g A)(i): lightP u A g i∈unitary _:=by
  obtain hh|hh:=h.1.sign i
  · rw [lightP,hh,one_smul]; exact wobble _ (Unitary.star_mem h.2.unit)
  rw [lightP,hh,neg_smul,one_smul]; constructor; all_goals simp only [star_neg,neg_mul_neg]; first| exact (wobble _ (Unitary.star_mem h.2.unit)).1 | exact (wobble _ (Unitary.star_mem h.2.unit)).2

def coin (v : Strut f) (a b : Site f →ℂ) (x : Site f):= b x*a (act v x)
lemma comb (hv:Warrant u g A)(hp:Warrant v h B): Warrant (pod u v) (coin v g h) (A*B):= by
  refine ⟨⟨fun i=>?_,fun i x=>?_⟩,hv.2.prod hp.2⟩
  · rcases hp.1.sign i with h|h <;> rcases hv.1.sign (act v i) with e|e <;> unfold coin <;> rw [h,e] <;> simp
  let a:= posDir i; have he: act v (x+step i)= affine v.1 v.2 x+ (a.rotate v.1).vec:= affine_add v.1 v.2 x a
  unfold coin; rw [← mul_assoc,hp.1.reflects,he,mul_assoc,glared hv.1]
  rw [show (pod u v).1=u.1*v.1 from rfl,← Step.rotate_mul,show affine u.1 u.2 (affine v.1 v.2 x)=affine (u.1*v.1) (pod u v).2 x from Eq.symm (Equiv.congr_fun (podA u v) x)] -- which motive?
  rw [mul_assoc]; rfl
lemma posture (g h:Site f→ℂ)(A B : Spike)(u v:Strut f)(x:Site f): lightP (pod u v) (A*B) (coin v g h) x=lightP v B h x*lightP u A g (act v x):=by
  simp only [lightP,star_mul,← wave_mul,Matrix.smul_mul,Matrix.mul_smul,coin, smul_smul, mul_comm (h x)]
lemma unique_scalar (hp:Warrant u g A)(hv:Warrant u h B):∃ c p:ℂ,c*c=1 ∧ star c=c∧ star p*p=1 ∧ A=p • B∧∀ i,g i=c*h i:=by
   obtain ⟨p,hp',hy⟩:=squad hp.2 hv.2
   refine ⟨g 0*h 0,p,?_,?_,hp',hy,fun i=> ?_⟩
   · rcases hp.1.sign 0 with h|h <;> rcases hv.1.sign 0 with e|e <;> rw [h,e] <;> simp
   · rcases hp.1.sign 0 with h|h <;> rcases hv.1.sign 0 with e|e <;> rw [h,e] <;> simp
   let w:= route 0 (lift i) 1
   have hstop : stop (0: Site f) w=i:=by unfold w; rw [wrap_stop,show stop _ _ =_ from route_end 0 (lift i) 1,wrap_lift,zero_add]
   have hi:=flare_path hp.1 w 0; have he:=flare_path hv.1 w 0; rw [hstop] at hi he
   let V:= shimmer 0 (0:Site f) w; have hN:V≠0:=by unfold V; rw [Quarry.occ_rays]; exact norm_ne_zero_iff.mp (by rw [Flume.pathLength]; norm_num)
   apply mul_left_cancel₀ hN; change shimmer _ _ _* _ = _; rw [hi]; rcases hv.1.sign 0 with e|e <;> rw [e] at he ⊢
   · rw [one_mul] at he; rw [← he]; unfold V; ring
   simp only [neg_mul,one_mul] at he; rw [← neg_neg (shimmer _ _ _),←he]; unfold V; ring
lemma mist (Q: Ratio c f)(v:Strut c)(hv: Warrant (raise Q v) g A): Warrant v (g ∘ Q.embed) A:=by
   refine ⟨shrouds Q ?_,hv.2⟩; rw [show Q.embed 0=0 from Q.root.map_zero]; exact hv.1
end Strut
end YM.QCD.Bay
