FROM python:3.11-alpine

RUN apk add --no-cache luau gcc musl-dev python3-dev libffi-dev

WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt --no-cache-dir
COPY bot.py .

CMD ["python", "bot.py"]
