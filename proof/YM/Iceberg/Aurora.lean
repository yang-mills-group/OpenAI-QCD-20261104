import YM.Gust.Sea
import YM.Roan.Peak
import YM.Sprig.Chap
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
abbrev Face:Type:=Axis×Axis
local notation "S"=> K.total
noncomputable def onceF (K: Choir): K.W→ₗ[ℂ]ℂ:= (K.total 1 0).toLinearMap 0 0
local notation "M"=> onceF K
lemma mint (v:K.W): S 1 0 (![v])= M v:=by
   apply congr_arg (K.total 1 _); ext i; fin_cases i; simp
lemma ones (v:K.W): M v=tone [(0,v)]:=by
   rw[←mint, ← grooved]; congr 1
include hf
lemma heartP (v:K.W)(p:EuPin)(s:Signed)(h:p.Lifts s): onceF K (T.spin p v)= M v:=by
     have hx:(0:Points 1)∈conf 1:=fun _ _ _=>Subsingleton.elim ..
     have he:= hf.discrete 1 0 hx p s h (![v]); rw [←mint,←mint,←he]; have hh:Points.move p.coord (0:Points 1)=0:=by ext1 i; exact map_zero (Ortho.motion _)
     rw [hh]; apply congr_arg; funext i; fin_cases i; rfl
variable (V:Face→K.W)(hv: Persona T V)
include hv
lemma trueY (i:Axis): M (V (0,0))= M (V (i,i)):=by
    let s:Signed:=⟨Equiv.swap 0 i, fun _=>false⟩; obtain ⟨p,hp⟩:= EuPin.choice s; rw [←heartP hf (p:=p) _ s hp,hv.tense.geo p s hp]; simp [s,signT]
lemma offW (a b:Axis)(h:a≠b): M (V (a,b))=0:=by
    let s:= Signed.mirror a; obtain ⟨p,hp⟩:= EuPin.choice s; have hg:=heartP hf (p:=p) (V (a,b)) s hp; rw [hv.tense.geo p s hp,map_smul] at hg; simp [s,signT,Signed.mirror,h] at hg; first | exact hg | exact neg_eq_self.mp hg
include hHQ
lemma honest (a:Axis):star (M (V (0,0)))=M (V (0,0)):=by
     let v:=V (0,0); have hh:Strip.distinct [(0,v)]:=(spots _).2 (by simp)
     have h:= crowned hHQ.h hf [(0,v)] hh a; simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_cons,List.map_nil,ChTag] at h; rw [←ones,←ones, show Ch T a v=v from stress_eye hHQ.h hf V hv a 0 0] at h; exact h.symm
omit hv
include hp hP ht
lemma primeB : M (lampU P K)=1:=by
     rw [← mint]; have he:points (![0]) = (0:Points 1):=by ext1 i; fin_cases i; rfl
     have hp0:= readU hp hP ht T hf hHQ; rw[he] at hp0; exact hp0
#check chartered
variable (hN:∀ d,∃ n:Lattice.Side, Injective (P.candidate d n 0))
include hN
lemma glows (a:Axis): roseC T a (tepid P K)=tepid P K:=by
     funext f; let B:=T.adj a; rcases f with ⟨i,j⟩; unfold roseC tepid; split
     next h=> cases (show i=j from h); rw [Complex.ofReal_mul, show (_:ℂ)*_=1 from mirror_sq a i, one_smul, show T.adj a _= _ from ?_]; unfold lampU; -- spins lemma
              obtain ⟨k,hk⟩:= hN 0; rw [T.a,Sprig.sendsAdj hP k hk]
     rw [map_zero,smul_zero]
include hv
local notation "TZ" => tepid P K
variable (hD:(swingE K 1).range=(bits K).range)(hX: Module.finrank ℂ (obσ 1 K).range=22)(hL:Module.finrank ℂ (bits K).range=20)
include hD hX hL
lemma baseN : ∃ W:Face→K.W,Persona T W∧∀ f,M (W f)=0:=by
     let c:= M (V (0,0)); let W:= V + (-c) • TZ; have hh:W=(1:ℂ) • V + (-c) • TZ:=by rw[one_smul]
     obtain ⟨ht₀,hr⟩:= (chartered hp hP ht T hf hHQ hD hX hL hN V W hv).2 ⟨1,-c,hh⟩ -- check order
     refine ⟨W,⟨ht₀,hr,?_,?_⟩,?_⟩
     · intro a; dsimp only[W]; rw[ray_add hp hP ht T hf hHQ a, ray_smul hp hP ht T hf hHQ a,star_neg, glows hp hP hHQ ht hf hN a,hv.real'a,show star c=c from honest hHQ hf V hv a]
     · intro z h; refine hv.non (z+c) ?_; rw [add_smul, ← h]; dsimp only [W]; rw[neg_smul]; abel
     rintro ⟨i,j⟩; unfold W; rw[Pi.add_apply,Pi.smul_apply,map_add,map_smul]; change _ + (-c) • M (if i=j then _ else _)=0; split
     next h=> subst j; rw [←trueY hf V hv i,primeB hp hP hHQ ht hf]; simp [c]
     next h=> rw [offW hf V hv i j h,map_zero,smul_zero,add_zero]
omit hv
end YM.Iceberg
#print axioms YM.Iceberg.baseN
