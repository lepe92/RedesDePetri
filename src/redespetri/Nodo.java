/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package redespetri;

import java.util.ArrayList;

/**
 *
 * @author HectorJalil, Edwin Jimenez, Ruben Barragan, Pedro, Ilse, Osvaldo,
 * Diego
 */
public class Nodo {

    boolean contieneW = false;
    int suma = 0;
    ArrayList<Nodo> hijos;
    int[] marcado;
    Nodo padre;
    // String tranDisparada;
    ArrayList<String> transicionDisparada = new ArrayList();
    boolean Terminal = false;
    boolean Duplicado = false;
    String color;
    int tiempoInicial;
    int tiempoFinal;

    public Nodo(int[] marcado, Nodo padre, String tran) {
        this.marcado = marcado;
        this.padre = padre;
        transicionDisparada.add(tran);
        hijos = new ArrayList();
        suma = sumarNodo();
        this.color = "WHITE";
        this.tiempoInicial = 0;
        this.tiempoFinal = 0;
    }
    
    //Sobreescrito.
    public Nodo(int[] marcado, Nodo padre, ArrayList trans) {
        this.marcado = marcado;
        this.padre = padre;
        transicionDisparada = trans;
        hijos = new ArrayList();
        suma = sumarNodo();
        this.color = "WHITE";
        this.tiempoInicial = 0;
        this.tiempoFinal = 0;
    }

    public void anadirTrans(String s) {
        transicionDisparada.add(s);
    }

    public void setMarcado(int m[]) {
        this.marcado = m;
    }

    public int sumarNodo() {
        suma = 0;
        for (int i = 0; i < marcado.length; i++) {
            if (marcado[i] == -1) {
                contieneW = true;
            } else {
                suma += marcado[i];
            }
        }
        return suma;
    }

    public void Print() {
        System.out.print("Marcado: ");
        for (int i = 0; i < marcado.length; i++) {
            System.out.print(marcado[i] + " ");
        }
        System.out.print("\n Transicion Disparada: " + transicionDisparada + "\n");
    }

    public String marcadoACadena() {
        String cad = "";
        for (int i = 0; i < marcado.length; i++) {
            if (marcado[i] == -1) {
                cad += "w";
            } else {
                cad += marcado[i];
            }

        }
        return "\"" + cad + "\"";
    }
}
