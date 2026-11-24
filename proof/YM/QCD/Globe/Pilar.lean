import YM.QCD.Globe.Boom
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {X:Sheet c}
lemma orchid (t:Strut c)(x:Site c)(u:Cover) : act t (x+wrap c u) = act t x+ wrap c (t.1.act u):=by
   change affine t.1 t.2 (x+wrap c u)= affine t.1 t.2 x+ wrap c (t.1.act u); unfold affine; rw [← wrap_signed,Signed.act_add]; abel
lemma standstill (hp:X=X)(T:Sheet c)(h:T∈unitary _)(he:aura T X=X): T*X=X*T:=by
   rw [show T*X=T*X*(star T*T) from by rw [h.1]; simp, ← Matrix.mul_assoc,Tmul] -- edit
 where Tmul : T*X*star T=X:=he
lemma Tempo.loft (h:Tempo X)(i j): cell X i j=wave (gold (cell X i j)):=by
   apply Stew.gilt; intro k; let p:Frame c:=fun _=>k; let Q:= siteRot p
   have hv₁(Y: Site c→Bundle)(U:Sheet c): cell (U* rides (Equiv.refl _) Y) i j=cell U i j *Y j:=by
       nth_rw 1 [← star_star (rides (Equiv.refl _) Y)]; rw [ride_ad, cell_ride_right, star_star]; rfl
   have hm:=congr_arg (fun X=>cell X i j) (standstill rfl Q (siteRot_u _) (h.hues _)); unfold Q siteRot at hm; rw [cell_ride_left,hv₁] at hm; exact hm
-- cover symbol samples all ties
noncomputable def onSet (X: Sheet c)(o: Site c)(w:Cover):Spike:= occ o w • gold (cell X o (o+wrap _ w))
noncomputable def onset (X: Sheet c)(o:Site c)(w:Cover): Bundle := occ o w • cell X o (o+wrap _ w)
lemma Tempo.giltV (h:Tempo X)(o w): onset X o w=wave (onSet X o w):=by
   unfold onset onSet; rw [show wave (_ • _)=_ from Matrix.smul_kronecker (occ o w) _ _]; exact congr_arg _ (h.loft o _)
lemma Tempo.visit (h:Tempo X)(o:Site c)(w:Cover) (t:Strut c)(p:Spike)(g:Site c→ℂ)(ht:Warrant t g p): onSet X (act t o) (t.1.act w)= p*onSet X o w*star p :=by
   let H:= haze t p g; have hC: star H*X*H=X:=by rw [← show aura (star H) X=star H*X*H from by unfold aura; rw [star_star]]; nth_rw 1 [← h.turns _ _ _ ht]; exact Orbit.compatible _ _ (trail ht)
   let V:= t; let A(x:Site c):=lightP V p g x
   let i:=o+ wrap _ w
   have hR: cell X (act t o) (act t i)=star (A o)*cell X o i*A i:=by nth_rw 1 [← hC]; exact billsL ..
   unfold onSet; rw [← orchid]
   have he:gold (cell X (act t o) (act t i))=(g o*g i) • (p*gold (cell X o i)*star p):=by rw [hR]; unfold A lightP; generalize hT:gold (cell X o i)=S; rw [h.loft o i,hT]; simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul,wave_star,star_star, wave_mul,smul_smul, gold_s,leafy]; rcases ht.1.sign o with h|h <;> simp [h,mul_comm]
   rw [he,Matrix.mul_smul,Matrix.smul_mul, smul_smul]; congr 1
   have hh: occ (act t o) (t.1.act w)*g o=g i *occ o w:= helmet o t w p g ht; rw [← mul_assoc,hh, mul_right_comm (g i)]; rcases ht.1.sign i with h|h<;> simp [h]
lemma Tempo.stillG (h: Tempo X)(o: Site c)(w:Cover): onSet X o w= onSet X 0 w:=by
     let t: Strut c:=(1,o); obtain ⟨p,hp⟩:=shades (1: Signed) (0:Site c) 0 o; have he : Warrant t p 1:=⟨hp,Swing.none⟩
     have hz:=h.visit 0 w t 1 p he; rw [show act t 0=o from ?_,one_mul,star_one,mul_one, show t.1.act w=w from Signed.act_one _] at hz; exact hz
     change affine 1 o 0=o; simp [affine]
lemma Tempo.rime (h:Tempo X)(o:Site c)(w: Cover): onSet X o w= g5*star (onSet X o (-w))*g5:=by
    let p:=o+wrap c w
    rw [h.stillG o (-w),← h.stillG p]; unfold onSet
    have hC: cell X o p=wave (g5*star (gold (cell X p o))*g5):=by
        nth_rw 1 [← h.song]; rw [newborn,aura,chirality,onSpin,cell_ride_right,cell_ride_left,Equiv.refl_apply,Equiv.refl_apply,show cell (star X) o p=star (cell X p o) from cell_flip ..]; change Lat.wave g5*star (cell X p o)*star (Lat.wave g5)=_
        generalize he: gold (cell X p o)=A; rw [h.loft p o,he,wave_star,wave_star,Lat.g5_star,wave_mul,wave_mul]
    rw [star_smul, (oaub _ p).2,Fork0,Matrix.mul_smul, Matrix.smul_mul, show p+wrap c (-w)=o from by unfold p; rw [map_neg]; abel]; exact congr_arg _ ((congr_arg Stew.gold hC).trans (leafy _))
 where Fork0 : occ (o+wrap c w) (-w)=occ o w:=folios w o
end YM.QCD.Globe
