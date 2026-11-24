import YM.QCD.Sparks.Brig

/-! # anchored linear all-cover vein. use sign tested at both levels, auxiliary
threshold entirely period proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume
open scoped Topology Matrix BigOperators Classical ContDiff
variable {n N:Side}{k:ℕ}
def page (x: Cnr n)(i : su.ColorIndex) : Flux:= fun l=> x (wrap n l.1, coord l.2,i)
def radial (x:Cover): Walk:= route 0 x 1
def limitAt (x:Cnr n)(N : Side): BaseSites su N := fun j=> bill (page x j.2.2) 0 (radial (lift j.1))
lemma repin (B:Window n N k)(x: Cnr n) (i:Road N): expandC B x i=x (B.cut i.1,i.2) := rfl
lemma rad_plan (x:Cover):stop 0 (radial x)=x:=route_end ..
lemma rad_length (x:Cover): (radial x).length=Laurent.size x:= Run.amounts ..

def pacify (B:Window n N k)(x : Cnr n): Cnr N:= expandC B x- gradientA su N (limitAt x N)
lemma pac (B:Window n N k)(x : Cnr n)(y:Site N)(i:Axis)(a: su.ColorIndex) : pacify B x (y,coord i,a)=x (B.cut y,coord i,a) + bill (page x a) 0 (radial (lift y))-bill (page x a) 0 (radial (lift (y+step i))):=by
  unfold pacify; simp only [Pi.sub_apply,repin,gradientA,LinearMap.pi_apply,LinearMap.sub_apply, show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i,LinearMap.proj_apply]; unfold limitAt; abel

def stanza (x:Stock): Walk:= (radial x.1++[posDir (axisEquiv.symm x.2)]) ++ Lattice.reverse (radial (x.1+step (axisEquiv.symm x.2)))
lemma poem (x:Stock):stop 0 (stanza x)=(0:Cover):=by
  let a:=axisEquiv.symm x.2
  unfold stanza; rw [stop_append,stop_append,rad_plan]; change stop (x.1+step a) (Lattice.reverse _)=_; nth_rw 1 [← rad_plan (x.1+step a)]; exact reverse_stop ..
lemma stanza_length (x:Stock): (stanza x).length ≤ 2*Laurent.size x.1+2:=by unfold stanza Lattice.reverse; rw [List.length_append,List.length_append,List.length_map,List.length_reverse,rad_length,rad_length]; have ht:= fees_end [posDir (axisEquiv.symm x.2)] x.1; simp only [stop, Step.vec_pos,List.length_cons,List.length_nil] at *; omega

def idyllic (p:Nub) (V:Cnr n):= bill (page V p.2.2) 0 (stanza (p.1,p.2.1))
lemma isp (B:Window n N k)(x:Cnr n)(p:Nub)(he:B.cut 0=0)(hv:Lattice.lift (wrap N p.1)=p.1)(hk: Lattice.lift (wrap N (p.1+step (axisEquiv.symm p.2.1)))=p.1+step (axisEquiv.symm p.2.1)):
    pacify B x ((wrap N p.1),p.2)=idyllic p x:=by
  let P:=p.1; let a:=axisEquiv.symm p.2.1
  let q : Stock:=(P,p.2.1); let Z:=page x p.2.2
  have hm:=rad_plan (P+step a)
  have hw : coord a=p.2.1:=axisEquiv.apply_symm_apply _
  rw [show p.2=(coord a,p.2.2) from Prod.ext hw.symm rfl,pac]; -- risk p
  have hp : bill Z 0 (stanza q)=bill Z 0 (radial P)+Z (P,a)-bill Z 0 (radial (P+step a)):=by
    have he := cancelled Z 0 (radial (P+step a))
    rw [hm] at he
    unfold stanza; rw [spendPath,stop_append,rad_plan]; change bill Z 0 (radial P++_) +bill Z (P+step a) _= _; rw [he, spendPath, rad_plan]; simp [bill,posDir,Step.used]; ring
  rw [show idyllic p x=_ from hp,hv,← show wrap N (p.1+step a)=wrap N p.1+step a from ((wrap N).map_add ..).trans (by rw [wrap_step]),hk]
  have hP:= B.port 0 p.1; rw [zero_add,he,zero_add] at hP; rw [hP]; unfold Z page; dsimp only [P]; rw [add_comm (x _)]

lemma paid_page (x:Cnr n)(a: su.ColorIndex)(z:Cover)(w:Walk):
    ‖bill (page x a) z w‖≤w.length*‖x‖:=by
  induction w generalizing z with
  | nil=> simp [bill]
  | cons d w ih=>
    rw [bill, List.length_cons]; push_cast; apply (norm_add_le ..).trans
    apply (add_le_add ?_ (ih _)).trans (le_of_eq (show ‖x‖+_= _ by ring))
    split <;> first | exact norm_le_pi_norm x _ | rw [norm_neg]; exact norm_le_pi_norm x _
lemma place_le (p:Cover): Laurent.size (lift (wrap N p)) ≤4 * Laurent.size p:=by
  apply (city_length _).trans
  have hp :=Eyrie.stopped (radial p) (0:Site N); rw [wrap_stop,rad_plan,zero_add,rad_length] at hp; omega
lemma spend_axis (B:Window n N k)(x:Cnr n)(p:Nub): ‖pacify B x (wrap N p.1,p.2)‖≤16*(1+Laurent.size p.1)*‖x‖:=by
  rcases p with ⟨v,i,j⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective i
  change ‖pacify B x ((wrap N) v,coord i,j)‖≤16*(1+Laurent.size v)*‖x‖
  let A:=page x j; let u:=wrap N v; let z:=u+step i
  have he (s:Cover): ‖bill A 0 (radial s)‖≤ Laurent.size s*‖x‖:= by rw [← rad_length s]; exact paid_page ..
  have ht : Laurent.size (lift z)≤4*(Laurent.size v+1):=by
    rw [show z=wrap N (v+step i) by simp [z,u]]
    have hh : Laurent.size (v+(posDir i).vec (R:=ℤ)) ≤ Laurent.size v+1:=by rw [← price_vec (posDir i)]; exact Laurent.size_add ..
    apply (place_le ..).trans; gcongr; exact hh
  rw [pac]; apply (norm_sub_le ..).trans; refine (add_le_add ((norm_add_le ..).trans (add_le_add (norm_le_pi_norm x _) (he _))) (he (lift z))).trans ?_
  have hv : (↑(Laurent.size (lift u)):ℝ)≤4*Laurent.size v:=by exact_mod_cast place_le (N:=N) v
  have hg : (↑(Laurent.size (lift z)):ℝ)≤ 4*(Laurent.size v+1):=by exact_mod_cast ht
  change ‖x‖+↑(Laurent.size (lift u))*‖x‖+↑(Laurent.size (lift z))*‖x‖ ≤ _; clear ht; nlinarith [norm_nonneg x, show (0:ℝ) ≤ Laurent.size v from by positivity]
end YM.QCD.Sparks
