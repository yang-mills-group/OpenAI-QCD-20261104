import YM.Tinus.RollerB
import YM.Portland.Border
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A:Type*}[Fintype A] {c f:Side}{j k F:ℕ}
open Finset
-- readout flat density.W.X.T.On.
lemma sectorize (X Y:Sour A)(x:Dirac A) : traceP (adapter X Y x)=Y.transpose*(traceP x * X):=by
     let B:= adapter X Y; have h(y:Dirac A)(j:A) : vary (.inl j) (B y)= ∑ k:A, X k j • B (vary (.inl k) y):=by unfold B adapter; rw [Sway.chain]; simp [Pairs,Fintype.sum_sum_type]
     have he(y:Dirac A)(j:A): vary (.inr j) (B y)=∑ k:A,Y k j • B (vary (.inr k) y):=by unfold B adapter; rw [Sway.chain]; simp [Pairs,Fintype.sum_sum_type]
     have hT(y:Dirac A): coef ∅ (B y)=coef ∅ y:= TorusPCAC.Ward.keeps_zero ..
     ext i j; change -(coef _ (vary (.inl j) (vary (.inr i) (B x))))=_; rw [he,map_sum,map_sum]; simp_rw [map_smul,h,map_sum,map_smul,hT]; rw[← sum_neg_distrib,Matrix.mul_apply]; refine sum_congr rfl fun k _=>?_ ; rw [Matrix.mul_apply, mul_sum]; simp_rw [smul_eq_mul,mul_sum]; rw [←sum_neg_distrib]; refine sum_congr rfl fun l _=>?_ ; change _= _*(-coef _ _ * _); simp only [Matrix.transpose_apply,pairD,LinearMap.comp_apply]; ring
open TorusPCAC.Geometry QCD.Revolve QCD.Flume QCD.Run
local notation "Qp"=> Massive.Run.plane
variable (b:Cover)(s:Site c)(l:Site c→ℂ)(h:Glare 1 (0:Site c) 0 s l)
local notation "Hb"=>heat (c:=c) b
include h
set_option maxHeartbeats 650000
lemma crystal (x y:Site c) : star (l x) *l y*(star (Qp (x+s))* Qp (y+s))= star (Qp x)*Qp y:=by
     have hp (k:Site c):star (Finch.violet k)*Finch.violet k=1:= by
          have ht:‖Finch.violet k‖=1:=by unfold Finch.violet; apply Laurent.mode_real; exact keyboard _|>.1
          rw [mul_comm]; exact (Complex.mul_conj (Finch.violet k)).trans (by simp [Complex.normSq_eq_norm_sq,ht])
     let d:= Stew.heel x y; let W:=route 0 d 1
     have hQ:Stew.heel (x+s) (y+s)=d:=by unfold d Stew.heel; rw [add_sub_add_right_eq_sub]
     have he: Stew.shine (x+s) (y+s)= shimmer (0:Site c) (x+s) (W.map (·.rotate 1)):=by
          apply Stew.shore; rw [hQ]; have hv:= moved_stop (1:Signed) (0:Cover) W; rw [Signed.act_one,Signed.act_one, show stop (0:Cover) W=d from route_end ..] at hv; exact hv.symm
     have hz: Stew.shine x y*l y=l x*Stew.shine (x+s) (y+s):=by
          rw [he]; have hf:= flare_path h W x; rw [Kit.wrap_stop,show stop (0:Cover) W=d from route_end ..,show x+wrap c d=y from (by unfold d Stew.heel; rw[wrap_lift]; abel),affine, Signed.act_one] at hf; exact hf
     have hM: Finch.modeP (x+s) (y+s)=Finch.modeP x y:=by unfold Finch.modeP; rw[hQ]
     have hy(i j:Site c): star (Qp i)* Qp j=Stew.shine i j*star (Finch.modeP i j):=by
           simp_rw [Massive.Reading.ray]; rw [Finch.pick i j,star_mul',star_mul',Stew.realSS,star_star]; let Q:= Finch.violet i; calc
                 _=(star Q * Q)*(Stew.shine i j*star (Finch.modeP i j)):=by unfold Q; ring
                 _=_:=by rw [show star Q * Q=1 from hp i,one_mul]
     rw[hy,hy,hM];
     rcases h.sign x with h1|h1<;> rcases h.sign y with h2|h2<;> rw [h1,h2] at hz ⊢ <;> simp at hz ⊢ <;> first | (solve|simp [hz]) | (rw [neg_eq_iff_eq_neg] at hz; simp [hz])
omit h
lemma angel (x y : Flavor 6)(T: Sheet c)(V: Sour (Modes c 6)) : piece x y (copies 6 T*V)= T*piece x y V:=by
     ext i j; rw [piece,Matrix.of_apply,Matrix.mul_apply, Matrix.mul_apply,Fintype.sum_prod_type]; unfold copies; simp [Matrix.blockDiagonal_apply,ite_mul]; -- `Finset` simplify `if p then`
lemma angie (x y:Flavor 6)(T:Sheet c)(V:Sour (Modes c 6)) : piece x y (V*copies 6 T)= piece x y V*T:=by
     ext i j; rw [piece,Matrix.of_apply,Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type]; unfold copies; simp [Matrix.blockDiagonal_apply,mul_ite]
-- inverse traces traction.Use for all densities.Even not required. No seam assumption beyond dimension.
lemma warmUp (b:Cover)(p:Density c 6)(X:Spike)(a d:Flavor 6)(g:ℂ): horn X a d g (Massive.Patria.march b p 1)= horn X a d g (p 1):=by
      let s:= wrap c b; let L:= heat b (n:=c); let A:= hues s 1 L 1; let M:= copies 6 A; let x:= p 1; let y:= Massive.Patria.march b p 1
      have hk:= glares (n:=c) b; have hA:A∈unitary _:=colour_wheel hk Swing.none; have hp:y= Kit.disguise M x:=by
           change Kit.disguise M (p (pull 1 s 1))=_; rw[show pull 1 s (1:Grid c)=1 from funext fun i=>by simp [pull,Step.read]]
      have hv : A*piece a d (traceP y)*star A= piece a d (traceP x):=by
           rw [hp,Kit.disguise,sectorize, Matrix.transpose_transpose,← Lat.copies_star]; change A*(piece a d (Lat.copies _ (star A)* (traceP x * Lat.copies _ A)))*star A=_; rw [angel, angie, ← mul_assoc A, hA.2,one_mul,mul_assoc,hA.2,mul_one]
      let v:= Equiv.addRight s
      have hx(i j:Site c): spinTest X i j (piece a d (traceP x))= L i* L j* spinTest X (v i) (v j) (piece a d (traceP y)):=by
           rw [← hv]; unfold spinTest; let p':= piece a d (traceP y); unfold A hues; rw [Bay.cell_ride_right,Bay.cell_ride_left]; have hi(t:Site c): shiftE 1 s t=t+s:=by simp [shiftE,Signed.actEquiv]
           simp_rw [hi,star_one,wave_one];
           rcases hk.sign i with h|h<;> rcases hk.sign j with hp|hp <;> change L i= _ at h<;>change L j=_ at hp<;> rw [h,hp] <;> simp [v]
      unfold horn; apply congr_arg (· / _); apply congr_arg (· / _); rw [←Equiv.sum_comp v]; refine sum_congr rfl fun i _=>?_ ; rw [←Equiv.sum_comp v]; refine sum_congr rfl fun j _=>?_ ; rw [hx]; let q:= spinTest X (v i) (v j) (piece a d (traceP y)); have hh := crystal s L hk i j; -- relation.
      change _*q*_= _; have hz: star (Qp (v i))*Qp (v j)=star (Qp i)*Qp j*(L i*L j):=by
               change star (Qp (i+s))*Qp (j+s)=_; rcases hk.sign i with h|h <;> rcases hk.sign j with hp|hp <;> change L i= _ at h <;>change L j= _ at hp <;> rw [h,hp] at hh ⊢ <;> simp at hh ⊢ <;> first| exact hh | exact neg_eq_iff_eq_neg.mp hh
      calc _= (star (Qp (v i))*Qp (v j))*q:= by ring
           _= _:=by rw [hz]; ring

end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.warmUp
