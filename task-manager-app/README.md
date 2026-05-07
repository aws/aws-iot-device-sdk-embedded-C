# Gestor de Tareas con Correo

App de una sola página (HTML/CSS/JS) que corre completamente en el navegador.

## Funcionalidades

- Crear tareas con título, descripción, prioridad y fecha límite.
- Marcar como completadas o eliminarlas.
- Filtrar (todas / pendientes / completadas) y borrar las completadas en lote.
- Persistencia local con `localStorage` (no necesita servidor).
- Enviar una tarea individual o un resumen filtrado por correo. Se abre el cliente
  de correo del usuario con un mensaje pre-llenado vía `mailto:`.

## Cómo correrla

Abrir `index.html` directamente en el navegador, o servirla localmente:

```bash
cd task-manager-app
python3 -m http.server 8000
# Luego abre http://localhost:8000
```

## Notas

- El envío usa `mailto:`, así que se necesita un cliente de correo configurado
  (Gmail web, Outlook, Apple Mail, Thunderbird, etc.) para que el botón abra el
  borrador. Esto evita necesitar un backend o claves de API.
- Las tareas viven en `localStorage` del navegador donde se creen.
