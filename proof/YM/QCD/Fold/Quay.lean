import YM.QCD.Fold.Verse
import YM.QCD.Port.Loft
/-! # Acquire stellar through the actual quilt mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{v:Strut F}{u:Strut f}{X:Patch} {e:f.val=c.val*X.L.val} {E:F.val=C.val*X.L.val} (h:C.val=c.val*D)(hl:2≤c.val)
variable (d:Site F→ℂ)
local notation "V"=> Lace.project (h:=e) (H:=E) h hl
local notation "r"=> decreed e
local notation "R"=> decreed E
local notation "L"=> Macrame.splitter (divides h)
-- first shore, implant
noncomputable def anchL:Collum f F (Site f) (Site F) (D^4) := {
  small:=id
  big:=id
  T:= (V).high
  pi:= (V).high.cut
  orient:=d
  d:=divides (fineP e E h)
  hv:=rfl
  nest i:=rfl
}
def pressL (d:Site F→ℂ):Collum f F (Site c) (Site C) (D^4):= {
  small:=(decreed e).embed
  big:= (R).embed
  T:= (V).high
  pi:= (V).low.cut
  orient:=d ∘ (R).embed
  d:=divides (fineP e E h)
  hv:=rfl
  nest i:= ((V).stake i).symm
}
variable (hd:Quaint (Lace.project (h:=e) (H:=E) h hl).high d)
include hd
lemma shores (u:Strut C)(v:Strut c)(hv:u.1=v.1)(ht:(V).low.cut u.2=v.2)(T:Spike)(f': Site f→ℂ)(hx: Warrant (raise r v) f' T): ∃ g, Warrant (raise R u) g T∧
     ((anchL (E:=E) (e:=e) h hl d).salt v u f' g (sun r) (sun R))∧ ((pressL (E:=E) (e:=e) h hl d).salt v u f' g (dot r) (dot R)):=by
   have hh : aims (V).low u v:=pegs (V).low (divides h) rfl hv ht
   have hp: (V).high.cut ((R).embed u.2)=(r).embed v.2:=by rw [(show (V).high.cut ((R).embed u.2)=_ from (V).stake _),ht]
   have hP:= pegs ((V).high) (divides (fineP e E h)) rfl (show (raise R u).1=(raise r v).1 from hv) (show (V).high.cut (raise R u).2=(raise r v).2 from hp)
   obtain ⟨g,hm,hg⟩:= belt (V).high hd hP T hx
   refine ⟨g,hm, ⟨hv,hP.2,fun i=> congr_fun hP.2 i,hg⟩,⟨hv,hP.2,fun i=>congr_fun hh.2 i,fun i=>?_⟩⟩
   have hz:=hg ((R).embed i); rw [peaks] at hz; exact hz

-- BAT fibre distribution pins
lemma issues (t:Strut c)(r':Site f→ℂ)(T:Spike)(hp:Warrant (raise r t) r' T): ∃ z w,Warrant (raise R z) w T ∧ ((anchL (E:=E) (e:=e) h hl d).salt t z r' w (sun r) (sun R)) ∧ ((pressL (E:=E) (e:=e) h hl d).salt t z r' w (dot r) (dot R)):=by
   obtain ⟨z,hz⟩:= Macrame.seeds (divides h) t.2; exact ⟨(t.1,z), shores _ _ _ hd (t.1,z) t rfl hz T r' hp⟩
open Collum
lemma dunes (p q:Site C)(hv:(V).low.cut p=(V).low.cut q):∃ w z, ((pressL (E:=E) (e:=e) h hl d).salt (pin r) w (fun _=>1) z (dot r) (dot R))∧ Warrant (raise R w) z 1∧ (dot R).shiftP w p=q:=by
   let u: Strut C:=(1,q-p); have ht: (V).low.cut (q-p)=0:=by change L _=0; rw [map_sub]; rw [show L p=L q from hv,sub_self]
   obtain ⟨g,hp,hG,hq⟩:= shores _ _ _ hd u (pin r) rfl ht 1 _ pin_cost; refine ⟨u,g,hq,hp,?_⟩; change affine 1 (q-p) p=q; simp [affine]
lemma peaksL (p q:Site F)(hv:(V).high.cut p=(V).high.cut q):∃ w z, ((anchL (E:=E) (e:=e) h hl d).salt (pin r) w (fun _=>1) z (sun r) (sun R))∧ Warrant (raise R w) z 1∧ (sun R).shiftP w p=q:=by
   let a:=(R).parent q-(R).parent p; have he := ((V).position p).symm.trans (hv ▸ (V).position q)
   have ht: (V).low.cut a=0:=by change L _=_; unfold a; rw [map_sub,show L ((R).parent p)=L ((R).parent q) from ?_,sub_self]; exact he
   obtain ⟨g,hp,hg,hq⟩:= shores _ _ _ hd (1,a) (pin r) rfl ht 1 _ pin_cost; refine ⟨(1,a),g,hg,hp,?_⟩
   have hh:(R).residue p=(R).residue q:= ((V).room p).symm.trans (hv ▸ (V).room q)
   change affine 1 ((R).embed a) p=q; suffices h : p+(R).embed a=q by simpa [affine] using h
   calc p+(R).embed a = (R).assemble ((R).parent p,(R).residue p)+(R).embed a :=  congr_arg₂ (· + ·) ((R).unpack_at p).symm rfl
        _ = (R).assemble ((R).parent q,(R).residue q):=by unfold Ratio.assemble a; dsimp only; rw [← (R).root_embed ((R).parent q-(R).parent p),map_sub,(R).root_embed,(R).root_embed,hh]; abel
        _ = q:= (R).unpack_at _
-- relation matrix constructor general
omit hd
lemma rule {c C:Side}{D:ℕ} (Z:Window c C D)(x:Site C→ℂ)(hx: Quaint Z x)(Rk:Sheet c)(Q:Sheet C)(hp:Q*stream Z x = stream Z x*Rk)(i j):
   cell Rk (Z.cut i) j=∑ K∈parcel Z.cut j, (star (x i)*x K) • cell Q i K:=by
  have hz :star (x i)*x i=1:=by rcases hx.sign i with h|h <;> rw [h]<;>simp
  ext p q; have ht:=(Matrix.ext_iff.mpr hp) (i,p) (j,q); rw [streams,Matrix.mul_apply,Fintype.sum_prod_type] at ht; rw [Matrix.sum_apply]; change Rk _ _=∑ K∈ parcel Z.cut j,(star (x i)*x K)*Q (i,p) (K,q)
  nth_rw 1 [show Rk (Z.cut i,p) (j,q)=star (x i)*(x i*Rk (Z.cut i,p) (j,q)) by rw [← mul_assoc,hz,one_mul], ← ht]; rw [mul_sum]
  unfold stream Shingle.parcel; rw [Finset.sum_filter]; apply sum_congr rfl; intro j' _; rw [sum_eq_single q] 
  · by_cases he: Z.cut j'=j<;> simp [he]<;>ring
  · intro i _ hi; simp [hi]
  simp
include hd
lemma line_support {Q:St f}{P:St F}(hp:∀ U:Grid f,P ((V).high.links U)*stream (V).high d=stream (V).high d*Q U): Collum.Receives (anchL (e:=e) (E:=E) h hl d) P Q:=by
   refine ⟨(V).high.fold,fun i=>?_,fun U i j=>rule _ _ hd _ _ (hp U) i j⟩
   rcases hd.sign i with h|h <;> change ‖d i‖=_<;>rw [h] <;>simp
end YM.QCD.Folding
#print axioms YM.QCD.Folding.peaksL
